partial def Substring.spanWithout (substr: Substring) (pred: Char → Bool): Substring × Substring :=
  let rec loop (i: String.Pos) :=
    if substr.atEnd i then
      (substr, substr.extract substr.stopPos substr.stopPos)
    else
      if pred $ substr.get i then
        loop (substr.next i)
      else
        (substr.extract 0 i, substr.extract (substr.next i) substr.stopPos)
  loop 0

partial def String.spanWithout (str: String) (pred: Char → Bool): Substring × Substring :=
  let rec loop (i: String.Pos) :=
    match str.get? i with
    | none =>
      let substr := str.toSubstring
      (substr, substr.extract str.endPos str.endPos)
    | some c =>
      if pred c then
        loop (str.next i)
      else
        let substr := str.toSubstring
        (substr.extract 0 i, substr.extract (str.next i) str.endPos)
  loop 0

structure RawReveal where
  red : Nat := 0
  green : Nat := 0
  blue : Nat := 0
deriving Repr

def parseReveal (substr: Substring): RawReveal :=
  let accum (acc: RawReveal) (ss: Substring) : RawReveal :=
    let (countSS, colorSS) := ss.trim.spanWithout (· ≠ ' ')
    match countSS.toNat? with
    | none => acc
    | some n =>
      if colorSS == "red".toSubstring then { acc with red := acc.red + n }
      else if colorSS == "green".toSubstring then { acc with green := acc.green + n }
      else if colorSS == "blue".toSubstring then { acc with blue := acc.blue + n }
      else acc
  List.foldl accum {} $ substr.splitOn ","

structure Reveal where
  red : { n : Nat // n ≤ 12 }
  green : { n : Nat // n ≤ 13 }
  blue : { n : Nat // n ≤ 14 }
deriving Repr

def parseGame (str: String): Nat × (List RawReveal) :=
  let (game, reveals) := str.spanWithout (· ≠ ':')
  ( game.spanWithout (· ≠ ' ') |>.2.toNat?.getD 0
  , reveals.splitOn ";" |>.map parseReveal
  )

inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : List ε → Validate ε α
deriving Repr

instance : Functor (Validate ε) where
  map f
    | .ok x => .ok (f x)
    | .errors errs => .errors errs

instance : Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok g => g <$> (x ())
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')

instance : Monad (Validate ε) where
  bind x f :=
    match x with
    | .errors errs => .errors errs
    | .ok x' => f x'

abbrev Field := String

def reportError (f: Field) (msg: String): Validate (Field × String) α :=
  .errors [(f, msg)]

def checkRed (n: Nat) : Validate (Field × String) { y: Nat // y <= 12 } :=
  if h: n <= 12 then
    pure ⟨ n, h ⟩
  else
    reportError "red" s!"Must be at most 12: Found {n}"

def checkGreen (n: Nat) : Validate (Field × String) { y: Nat // y <= 13 } :=
  if h: n <= 13 then
    pure ⟨ n, h ⟩
  else
    reportError "green" s!"Must be at most 13: Found {n}"

def checkBlue (n: Nat) : Validate (Field × String) { y: Nat // y <= 14 } :=
  if h: n <= 14 then
    pure ⟨ n, h ⟩
  else
    reportError "blue" s!"Must be at most 14: Found {n}"

def validateReveal (raw: RawReveal) : Validate (Field × String) Reveal :=
  pure Reveal.mk <*> checkRed raw.red <*> checkGreen raw.green <*> checkBlue raw.blue

def validateGame (str: String): Nat :=
  let (val, raw) := parseGame str
  let validations := raw.map validateReveal
  let failed : Validate (Field × String) Reveal → Bool
    | .ok _ => false
    | .errors _ => true
  if validations.any failed then 0
  else val

def RawReveal.min (reveals: List RawReveal): RawReveal :=
  let accum (acc: RawReveal) (a: RawReveal): RawReveal :=
    { red   := max acc.red a.red
    , green := max acc.green a.green
    , blue  := max acc.blue a.blue
    }
  reveals.foldl accum {}

def RawReveal.power (reveal: RawReveal) : Nat :=
  reveal.red * reveal.green * reveal.blue

def powerGame (str: String): Nat :=
  RawReveal.power ∘ RawReveal.min ∘ Prod.snd ∘ parseGame $ str

partial def sumGames (fn: String → Nat) (acc: Nat) (stream: IO.FS.Stream) : IO Nat := do
  let line ← stream.getLine
  if line.isEmpty then pure acc else
    let gameSum := fn line
    sumGames fn (acc + gameSum) stream

def fileStream (filename: System.FilePath) : IO (Option IO.FS.Stream) := do
  let fileExists ← filename.pathExists
  if not fileExists then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure $ some $ IO.FS.Stream.ofHandle handle

def handleIO (fn: String → Nat) (acc: Nat) (exitCode: UInt32) (args: List String) : IO UInt32 := do
  match args with
  | [] =>
    println! s!"Result: {acc}"
    pure exitCode
  | "-" :: args =>
    let stdin ← IO.getStdin
    let acc' ← sumGames fn acc stdin
    handleIO fn acc' exitCode args
  | filename :: args =>
    let stream ← fileStream filename
    match stream with
    | none => handleIO fn acc 2 args
    | some stream =>
      let acc' ← sumGames fn acc stream
      handleIO fn acc' exitCode args

def main : List String → IO UInt32
  | [] => handleIO (powerGame) 0 0 ["-"]
  | version :: args =>
    let args' := match args with
    | [] => ["-"]
    | _ => args
    match version with
    | "V1" => handleIO (validateGame) 0 0 args'
    | "V2" => handleIO (powerGame) 0 0 args'
    | _ => handleIO (powerGame) 0 0 (version :: args)
