universe u v

def List.duplicate {α: Type u} : List α → List (List α)
  | [] => []
  | x :: xs => (x :: xs) :: duplicate xs

def getDigit : List Char → Option Char
  | [] => none
  | c :: cs => if c.isDigit then some c else getDigit cs

def getParsedDigit : List Char → Option Char
  | [] => none
  | 'z' :: 'e' :: 'r' :: 'o' :: _ => some '0'
  | 'o' :: 'n' :: 'e' :: _ => some '1'
  | 't' :: 'w' :: 'o' :: _ => some '2'
  | 't' :: 'h' :: 'r' :: 'e' :: 'e' :: _ => some '3'
  | 'f' :: 'o' :: 'u' :: 'r' :: _ => some '4'
  | 'f' :: 'i' :: 'v' :: 'e' :: _ => some '5'
  | 's' :: 'i' :: 'x' :: _ => some '6'
  | 's' :: 'e' :: 'v' :: 'e' :: 'n' :: _ => some '7'
  | 'e' :: 'i' :: 'g' :: 'h' :: 't' :: _ => some '8'
  | 'n' :: 'i' :: 'n' :: 'e' :: _ => some '9'
  | c :: cs => if c.isDigit then some c else getParsedDigit cs

def getFirst {α: Type u} (fn: List Char → Option α) (lists: List (List Char)) : Option α :=
  match lists with
  | [] => none
  | cs :: css => match fn cs with
    | some a => some a
    | none => getFirst fn css

def getCalibration? (fn: List Char → Option Char) (str: String) : Option Nat := do
  let cochars := str.toList.duplicate
  let lhs ← getFirst fn cochars
  let rhs ← getFirst fn cochars.reverse
  [lhs, rhs].asString.toNat?

def getCalibration (fn: List Char → Option Char) (str: String) : Nat :=
  getCalibration? fn str |>.getD 0

partial def sumCalibrations (fn: String → Nat) (acc: Nat) (stream: IO.FS.Stream) : IO Nat := do
  let line ← stream.getLine
  if line.isEmpty then pure acc else
    let calibration := fn line
    sumCalibrations fn (acc + calibration) stream

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
    let acc' ← sumCalibrations fn acc stdin
    handleIO fn acc' exitCode args
  | filename :: args =>
    let stream ← fileStream filename
    match stream with
    | none => handleIO fn acc 2 args
    | some stream =>
      let acc' ← sumCalibrations fn acc stream
      handleIO fn acc' exitCode args

def main : List String → IO UInt32
  | [] => handleIO (getCalibration getParsedDigit) 0 0 ["-"]
  | version :: args =>
    let args' := match args with
    | [] => ["-"]
    | _ => args
    match version with
    | "V1" => handleIO (getCalibration getDigit) 0 0 args'
    | "V2" => handleIO (getCalibration getParsedDigit) 0 0 args'
    | _ => handleIO (getCalibration getParsedDigit) 0 0 (version :: args)
