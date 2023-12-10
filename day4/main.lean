abbrev Parser := StateT (List Char) $ Except String

def parseFirst : Parser Char
  | [] => throw "No more characters to parse"
  | c :: cs => pure $ ⟨ c, cs ⟩

def parseIf (p: Char → Bool) : Parser Char := do
  let char ← parseFirst
  if p char then return char
  throw "parseIf failed"

def parseChar (c: Char) : Parser Char := parseIf (·=c)

def parseString (str: String) : Parser String :=
  str.toList.mapM parseChar |>.map List.asString

def parseDigit : Parser Char := parseIf Char.isDigit

mutual
  partial def parseAny (p: Parser α) : Parser $ List α :=
    parseSome p <|> pure []

  partial def parseSome (p: Parser α) : Parser $ List α := do
    let x ← p
    let xs ← parseAny p
    pure $ x :: xs
end

def parseWhitespace : Parser $ List Char := parseAny $ parseIf Char.isWhitespace

def parseNat : Parser Nat :=
  parseSome parseDigit
  |>.map (String.toNat! ∘ List.asString)

def parseSep (sep: Parser α) (p: Parser β) : Parser $ List β :=
  parseAny $ p <* sep

def parseCard : Parser $ List Nat := do
  let _ ← parseString "Card" *> parseWhitespace *> parseNat
  let targets ← parseString ":" *> parseWhitespace *> parseSep parseWhitespace parseNat
  let lottery ← parseString "| " *> parseWhitespace *> parseSep parseWhitespace parseNat
  return lottery.filter (· ∈ targets)

def countCard : Parser Nat := do
  let winners ← parseCard
  return winners.length

def List.takeSum (n: Nat) (arr: List Nat) : Nat :=
  arr.take n |>.foldl Nat.add 0

def countCards (count: List Nat): Id Nat := do
  let mut cache : List Nat := []
  for i in count.reverse do
    let sum := cache.takeSum i
    cache := (sum + 1) :: cache
  cache.foldl Nat.add 0

def evalCard: Parser Nat := do
  let winners ← parseCard
  return winners.foldl (λ acc _ => if acc = 0 then 1 else acc * 2) 0

partial def countWinners (acc: Array Nat) (stream: IO.FS.Stream) : IO $ List Nat := do
  let line ← stream.getLine
  if line.isEmpty then return acc.toList

  match countCard line.toList with
  | .ok (val, _) => countWinners (acc.push val) stream
  | .error e =>
    println! s!"Error: {e}"
    return acc.toList

partial def evalCards (acc: Nat) (stream: IO.FS.Stream) : IO Nat := do
  let line ← stream.getLine
  if line.isEmpty then return acc

  match evalCard line.toList with
  | .ok (val, _) => evalCards (acc + val) stream
  | .error e =>
    println! s!"Error: {e}"
    return acc

def fileStream (filename: System.FilePath) : IO (Option IO.FS.Stream) := do
  let fileExists ← filename.pathExists
  if not fileExists then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found {filename}"
    return none

  let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
  return some $ IO.FS.Stream.ofHandle handle

def handleCount (acc: Nat) (exitCode: UInt32) (args: List String) : IO UInt32 := do
  match args with
  | [] =>
    println! s!"Result: {acc}"
    return exitCode
  | "-" :: args =>
    let stdin ← IO.getStdin
    let acc' ← countWinners #[] stdin
    let result := countCards acc' |>.run
    handleCount (acc + result) exitCode args
  | filename :: args =>
    let stream ← fileStream filename
    match stream with
    | none => handleCount acc 2 args
    | some stream =>
      let acc' ← countWinners #[] stream
      let result := countCards acc' |>.run
      handleCount (acc + result) exitCode args

def handleIO (acc: Nat) (exitCode: UInt32) (args: List String) : IO UInt32 := do
  match args with
  | [] =>
    println! s!"Result: {acc}"
    return exitCode
  | "-" :: args =>
    let stdin ← IO.getStdin
    let acc' ← evalCards acc stdin
    handleIO acc' exitCode args
  | filename :: args =>
    let stream ← fileStream filename
    match stream with
    | none => handleIO acc 2 args
    | some stream =>
      let acc' ← evalCards acc stream
      handleIO acc' exitCode args

def main : List String → IO UInt32
  | [] => handleCount 0 0 ["-"]
  | version :: args =>
    let args' := match args with
    | [] => ["-"]
    | _ => args
    match version with
    | "V1" => handleIO 0 0 args'
    | "V2" => handleCount 0 0 args'
    | _ => handleCount 0 0 (version :: args)
