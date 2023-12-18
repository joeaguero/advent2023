import Lean.Data.Parsec
open Lean

def advent : String :=
"seeds: 79 14 55 13

seed-to-soil map:
50 98 2
52 50 48

soil-to-fertilizer map:
0 15 37
37 52 2
39 0 15

fertilizer-to-water map:
49 53 8
0 11 42
42 0 7
57 7 4

water-to-light map:
88 18 7
18 25 70

light-to-temperature map:
45 77 23
81 45 19
68 64 13

temperature-to-humidity map:
0 69 1
1 0 69

humidity-to-location map:
60 56 37
56 93 4"

def Parsec.nat : Parsec Nat := do
  String.toNat! <$> Parsec.digit.many1Chars <* Parsec.ws

def Parsec.seed_header : Parsec String :=
  Parsec.pstring "seeds:" <* Parsec.ws

def Parsec.seeds : Parsec $ Array Nat := do
  Parsec.seed_header *> Parsec.many Parsec.nat

structure SeedRange where
  beg: Nat
  size: Nat
deriving Repr

def Parsec.seed_ranges : Parsec $ Array SeedRange := do
  Parsec.seed_header *> Parsec.many (SeedRange.mk <$> Parsec.nat <*> Parsec.nat)

structure Mapping where
  dest: Nat
  source: Nat
  range: Nat
deriving Repr

def Parsec.mappings (pair: String × String) : Parsec $ Array Mapping := do
  let (from_str, to_str) := pair
  let _ ← Parsec.pstring s!"{from_str}-to-{to_str} map:" <* Parsec.ws
  Parsec.many $ Mapping.mk
    <$> Parsec.nat
    <*> Parsec.nat
    <*> Parsec.nat

def mapSeeds (seeds: Array Nat) (mappings: Array Mapping) : Array Nat :=
  seeds.mapMono $ λ seed ↦
    let mapping? := mappings.find? $ λ mapping ↦
      seed >= mapping.source && seed < mapping.source + mapping.range
    match mapping? with
    | none => seed
    | some mapping => seed - mapping.source + mapping.dest

def mapSeedRanges (ranges: Array SeedRange) (mappings: Array Mapping) : Array SeedRange := Id.run do
  let loop (state: (Array SeedRange) × (Array SeedRange)) (mapping: Mapping): (Array SeedRange) × (Array SeedRange) := Id.run do
    let mut completed ← state.1
    let mut remaining ← #[]
    for range in state.2 do
      let range_end := range.beg + range.size
      let mapping_end := mapping.source + mapping.range

      if range_end < mapping.source || range.beg ≥ mapping_end then
        remaining := remaining.push range
        continue

      let lhs := max range.beg mapping.source
      let rhs := min range_end mapping_end

      if lhs > range.beg then remaining := remaining.push (⟨ range.beg, lhs - range.beg ⟩: SeedRange)
      completed := completed.push ⟨ mapping.dest + (lhs - mapping.source) , rhs - lhs ⟩
      if rhs < range_end then remaining := remaining.push (⟨ rhs, range_end - rhs ⟩: SeedRange)

    return ⟨ completed, remaining ⟩
  let out := mappings.foldl loop (#[], ranges)
  out.1 ++ out.2

def List.pair : List α → List (α × α)
  | [] => []
  | [_] => []
  | a :: b :: rest => (a, b) :: pair (b :: rest)

def transitions :=
  [ "seed"
  , "soil"
  , "fertilizer"
  , "water"
  , "light"
  , "temperature"
  , "humidity"
  , "location"
  ].pair

def Parsec.almanac : Parsec Nat := do
  let seeds ← Parsec.seeds
  let parsers ← transitions.mapM Parsec.mappings
  let locations := parsers.foldl mapSeeds seeds

  match locations.toList with
  | [] => return 0
  | location :: rest => return rest.foldl min location

def Parsec.almanac_ranges : Parsec Nat := do
  let seeds ← Parsec.seed_ranges
  let parsers ← transitions.mapM Parsec.mappings
  let locations := parsers.foldl mapSeedRanges seeds

  match locations.toList with
  | [] => return 0
  | location :: rest => return rest.foldl (λ acc cur ↦ min cur.beg acc) location.beg

partial def accEngine (acc: String) (stream: IO.FS.Stream) : IO String := do
  let line ← stream.getLine
  if line.isEmpty then return acc
  if acc.length = 0 then
    accEngine line stream
  else
    accEngine (s!"{acc}\n{line}") stream

def fileStream (filename: System.FilePath) : IO (Option IO.FS.Stream) := do
  let fileExists ← filename.pathExists
  if not fileExists then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure $ some $ IO.FS.Stream.ofHandle handle

def handleIO (parser: Parsec Nat) (acc: Option Nat) (exitCode: UInt32) (args: List String) : IO UInt32 := do
  match args with
  | [] =>
    println! s!"Result: {acc}"
    pure exitCode
  | "-" :: args =>
    let stdin ← IO.getStdin
    let str ← accEngine "" stdin
    let acc' := parser.run str
    match acc' with
    | Except.error err =>
      println! err
      handleIO parser acc 3 args
    | Except.ok acc' =>
      match acc with
      | none => handleIO parser acc' exitCode args
      | some acc => handleIO parser (some $ min acc acc') exitCode args
  | filename :: args =>
    let stream ← fileStream filename
    match stream with
    | none => handleIO parser acc 2 args
    | some stream =>
      let str ← accEngine "" stream
      let acc' := parser.run str
      match acc' with
      | Except.error err =>
        println! err
        handleIO parser acc 3 args
      | Except.ok acc' =>
        match acc with
        | none => handleIO parser acc' exitCode args
        | some acc => handleIO parser (some $ min acc acc') exitCode args

def main : List String → IO UInt32
  | [] => handleIO Parsec.almanac_ranges none 0 ["-"]
  | version :: args =>
    let args' := match args with
    | [] => ["-"]
    | _ => args
    match version with
    | "V1" => handleIO Parsec.almanac none 0 args'
    | "V2" => handleIO Parsec.almanac_ranges none 0 args'
    | _ => handleIO Parsec.almanac_ranges none 0 (version :: args)

