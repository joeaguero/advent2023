import Lean.Data.Parsec
open Lean

def Parsec.nat : Parsec Nat :=
  String.toNat! <$> Parsec.many1Chars Parsec.digit

def Parsec.int : Parsec Int :=
  (Parsec.pchar '-' *> (-1 * Int.ofNat ·) <$> Parsec.nat)
  <|> Int.ofNat <$> Parsec.nat

def Parsec.line : Parsec $ Array Int := do
  let fst <- Parsec.int
  let rest <- Parsec.many $ Parsec.pchar ' ' *> Parsec.int
  return rest.insertAt 0 fst

def Array.toDiff (arr: Array Int) : Array Int := Id.run do
  let mut res := #[]

  if arr.size > 0 then
    for i in [1:arr.size] do
      res := res.push $ arr[i]! - arr[i-1]!

  return res

def Array.eval (arr: Array Int) : Int := Id.run do
  let mut current := arr
  let mut stack := #[]

  repeat do
    if current.all (· = 0) then break
    stack := stack.push $ current.get! $ current.size - 1
    current := current.toDiff

  return stack.foldr Int.add 0

def Array.evalR (arr: Array Int) : Int := Id.run do
  let mut current := arr
  let mut stack := #[]

  repeat do
    if current.all (· = 0) then break
    stack := stack.insertAt 0 $ current.get! 0
    current := current.toDiff

  return stack.foldl (flip Int.sub) 0

def Parsec.history : Parsec Int := do
  let line <- Parsec.line
  return line.eval

def Parsec.historyR : Parsec Int := do
  let line <- Parsec.line
  return line.evalR

def evalLine (p: Parsec Int) (stream: IO.FS.Stream) : IO Int := do
  let mut history := 0

  repeat do
    let line ← stream.getLine
    if line.isEmpty then break
    match p.run line with
    | .ok h => history := history + h
    | .error _ => break

  return history

def fileStream (filename: System.FilePath) : IO (Option IO.FS.Stream) := do
  let fileExists ← filename.pathExists
  if not fileExists then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found {filename}"
    return none

  let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
  return some $ IO.FS.Stream.ofHandle handle

def handleIO (p: Parsec Int) (acc: Int) (exitCode: UInt32) (args: List String) : IO UInt32 := do
  match args with
  | [] =>
    println! s!"Result: {acc}"
    return exitCode

  | "-" :: args =>
    let stdin ← IO.getStdin
    let acc' ← evalLine p stdin
    handleIO p (acc + acc') exitCode args

  | filename :: args =>
    let stream ← fileStream filename
    match stream with
    | none => handleIO p acc 1 args
    | some stream =>
      let acc' ← evalLine p stream
      handleIO p (acc + acc') exitCode args

def main : List String → IO UInt32
  | [] => handleIO Parsec.historyR 0 0 ["-"]
  | version :: args =>
    let args' := match args with
    | [] => ["-"]
    | _ => args
    match version with
    | "V1" => handleIO Parsec.history 0 0 args'
    | "V2" => handleIO Parsec.historyR 0 0 args'
    | _ => handleIO Parsec.historyR 0 0 (version :: args)

