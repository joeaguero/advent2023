import Lean.Data.HashMap
import Lean.Data.Parsec
open Lean

inductive Navigation where
  | Left | Right
deriving Repr

instance : ToString Navigation where
  toString
  | .Left => "L"
  | .Right => "R"

def Parsec.navigation : Parsec Navigation := do
  let c ← Parsec.asciiLetter
  match c with
  | 'L' => return Navigation.Left
  | 'R' => return Navigation.Right
  | _ => Parsec.fail "expected L or R"

def Parsec.path : Parsec { arr: Array Navigation // arr.size > 0 } := do
  let nav <- Parsec.many1 Parsec.navigation <* Parsec.ws

  if h: nav.size > 0 then return ⟨ nav, h ⟩
  else Parsec.fail "Invalid path"

abbrev Token := { str : String // str.length = 3 }

def Parsec.token : Parsec Token := do
  let c1 ← Parsec.anyChar
  let c2 ← Parsec.anyChar
  let c3 ← Parsec.anyChar
  return ⟨ s!"{c1}{c2}{c3}", by rfl ⟩

def Parsec.fork : Parsec $ Token × Token := do
  let left ← Parsec.pchar '(' *> Parsec.token
  let right ← Parsec.pchar ',' *> Parsec.ws *> Parsec.token <* Parsec.pchar ')' <* Parsec.ws
  return (left, right)

structure MapLine where
  key: Token
  directions: Token × Token
deriving Repr

def Parsec.mapLine : Parsec MapLine :=
  MapLine.mk
  <$> Parsec.token <* Parsec.ws <* Parsec.pchar '=' <* Parsec.ws
  <*> Parsec.fork

def Parsec.map : Parsec $ HashMap Token (Token × Token) := do
  let mut map := HashMap.empty

  for ⟨ key, directions ⟩ in (← Parsec.many1 Parsec.mapLine) do
    map := map.insert key directions

  return map

def Parsec.follow : Parsec Nat := do
  let steps ← Parsec.path
  let map ← Parsec.map
  let mut selected: Token := ⟨ "AAA", by rfl ⟩
  let mut count: Nat := 0

  while selected.val ≠ "ZZZ" do
    match map.find? selected with
    | none => Parsec.fail "Invalid map"
    | some (lhs, rhs) =>
      let step := steps.val.get (Fin.ofNat' count steps.2)

      match step with
      | .Left => selected := lhs
      | .Right => selected := rhs

      count := count + 1

  return count

def Nat.lcm : Nat -> Nat -> Nat
  | 0, _ => 0
  | _, 0 => 0
  | a, b => a * b / (a.gcd b)

def getPeriod (steps: { arr: Array Navigation // arr.size > 0}) (map: HashMap Token (Token × Token)) (selected: Token) : Nat := Id.run do
  let mut count: Nat := 0
  let mut current: Token := selected

  repeat do
    if current.val.get! ⟨ 2 ⟩ = 'Z' then break

    match map.find? current with
    | none => break -- expected unreachable
    | some (lhs, rhs) =>
      let step := steps.1.get (Fin.ofNat' count steps.2)
      match step with
      | .Left => current := lhs
      | .Right => current := rhs

    count := count + 1

  return count

def Parsec.follows : Parsec Nat := do
  let steps <- Parsec.path
  let map <- Parsec.map
  let starting := map.toList.filterMap $ λ (key, _) => if key.val.get! ⟨ 2 ⟩ = 'A' then some key else none
  let periods := starting.map $ getPeriod steps map
  return periods.foldl Nat.lcm 1

def advent: String :=
"LR

11A = (11B, XXX)
11B = (XXX, 11Z)
11Z = (11B, XXX)
22A = (22B, XXX)
22B = (22C, 22C)
22C = (22Z, 22Z)
22Z = (22B, 22B)
XXX = (XXX, XXX)"

def evalLine (stream: IO.FS.Stream) : IO String := do
  let mut lines := #[]

  repeat do
    let line ← stream.getLine
    if line.isEmpty then break
    lines := lines.push line

  return String.join lines.toList

def fileStream (filename: System.FilePath) : IO (Option IO.FS.Stream) := do
  let fileExists ← filename.pathExists
  if not fileExists then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found {filename}"
    return none

  let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
  return some $ IO.FS.Stream.ofHandle handle

def handleIO (p: Parsec Nat) (acc: Nat) (exitCode: UInt32) (args: List String) : IO UInt32 := do
  match args with
  | [] =>
    println! s!"Result: {acc}"
    return exitCode

  | "-" :: args =>
    let stdin ← IO.getStdin
    let acc' ← evalLine stdin
    let result := p.run acc'
    match result with
    | .ok acc' => handleIO p (acc + acc') exitCode args
    | .error _ => handleIO p acc 1 args

  | filename :: args =>
    let stream ← fileStream filename
    match stream with
    | none => handleIO p acc 2 args
    | some stream =>
      let acc' ← evalLine stream
      let result := p.run acc'
      match result with
      | .ok acc' => handleIO p (acc + acc') exitCode args
      | .error _ => handleIO p acc 3 args

def main : List String → IO UInt32
  | [] => handleIO Parsec.follows 0 0 ["-"]
  | version :: args =>
    let args' := match args with
    | [] => ["-"]
    | _ => args
    match version with
    | "V1" => handleIO Parsec.follow 0 0 args'
    | "V2" => handleIO Parsec.follows 0 0 args'
    | _ => handleIO Parsec.follows 0 0 (version :: args)

