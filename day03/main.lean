open List

inductive Groups (α : Type) : Type :=
  | single: α → Groups α
  | top : α → α → Groups α
  | bottom : α → α → Groups α
  | middle : α → α → α → Groups α
deriving Repr

def group {α : Type } (list: List α) : List (Groups α) :=
  let rec loop (prior₁ prior₂: α) (rest : List α) : List (Groups α) :=
    match rest with
    | [] => [Groups.bottom prior₁ prior₂]
    | [a] => [Groups.middle prior₁ prior₂ a, Groups.bottom prior₂ a]
    | a :: as => Groups.middle prior₁ prior₂ a :: loop prior₂ a as

  match list with
  | [] => []
  | [a] => [Groups.single a]
  | [a, b] => [Groups.top a b, Groups.bottom a b]
  | a :: b :: rest => Groups.top a b :: loop a b rest

def traverse (group: Groups (List α)) : List (Groups α) :=
  match group with
  | .single chars =>
    List.map Groups.single chars
  | .top chars chars' =>
    List.zipWith Groups.top chars chars'
  | .bottom chars' chars =>
    List.zipWith Groups.bottom chars' chars
  | .middle chars₁ chars chars₂ =>
    List.zipWith (λ lhs rhs ↦ Groups.middle lhs rhs.1 rhs.2) chars₁ $ List.zip chars chars₂

instance : Monad List where
  pure := List.pure
  bind := List.bind

structure ParseState where
  digits : List Char := []
  isValid: Bool := False
  total : Nat := 0
deriving Repr

def ParseState.calculateDigits (p: ParseState) : Nat :=
  if p.isValid then
    let new := p.digits.asString.toNat? |>.getD 0
    p.total + new
  else p.total

def Char.isSymbol (chr: Char) : Bool :=
  not (chr.isWhitespace || chr.isAlpha || chr.isDigit)

def Char.isSignal (char: Char) : Bool :=
  char.isSymbol && char != '.'


def sumGroup (chars: List (Groups Char)) : Nat :=
  let accumulate (acc: ParseState) (char: Char) (context: List Char) : ParseState :=
    if char.isDigit then { acc with digits:= acc.digits ++ [char], isValid:=acc.isValid || context.any Char.isSignal }
    else if List.any (char :: context) Char.isSignal then
      { isValid:=True, total:={acc with isValid:=True}.calculateDigits }
    else { total:= acc.calculateDigits }
  let reduce (acc: ParseState) (cur: Groups Char) : ParseState :=
    match cur with
    | .single char => accumulate acc char []
    | .top char context => accumulate acc char [context]
    | .bottom context char => accumulate acc char [context]
    | .middle context₁ char context₂ => accumulate acc char [context₁, context₂]

  chars.foldl reduce {} |>.calculateDigits

def sumValidDigits (strs: List String): Nat :=
  let mapped := do
    let group ← group $ strs.map String.toList
    let chars := traverse group
    pure $ sumGroup chars
  mapped.foldl (·+·) 0

partial def accEngine (acc: Array String) (stream: IO.FS.Stream) : IO (Array String) := do
  let line ← stream.getLine
  if line.isEmpty then pure acc else
    accEngine (acc.push line) stream

def fileStream (filename: System.FilePath) : IO (Option IO.FS.Stream) := do
  let fileExists ← filename.pathExists
  if not fileExists then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure $ some $ IO.FS.Stream.ofHandle handle

def handleIO (acc: Nat) (exitCode: UInt32) (args: List String) : IO UInt32 := do
  match args with
  | [] =>
    println! s!"Result: {acc}"
    pure exitCode
  | "-" :: args =>
    let stdin ← IO.getStdin
    let arr ← accEngine [].toArray stdin
    let acc' := sumValidDigits arr.toList
    handleIO acc' exitCode args
  | filename :: args =>
    let stream ← fileStream filename
    match stream with
    | none => handleIO acc 2 args
    | some stream =>
      let arr ← accEngine [].toArray stream
      let acc' := sumValidDigits arr.toList
      handleIO acc' exitCode args

def main : List String → IO UInt32
  | [] => handleIO 0 0 ["-"]
  | version :: args =>
    let args' := match args with
    | [] => ["-"]
    | _ => args
    match version with
    | "V1" => handleIO 0 0 args'
    | "V2" => handleIO 0 0 args'
    | _ => handleIO 0 0 (version :: args)
