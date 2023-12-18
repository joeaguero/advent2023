import Lean.Data.Parsec

open Lean

def advent : String :=
"Time:        49     97     94     94
Distance:   263   1532   1378   1851"

def between (pair: Float × Float) : Nat :=
  let bottom := Float.floor pair.1
  let top := Float.ceil pair.2
  let result := max top bottom - min top bottom |>.toUInt64.toNat
  result - 1

structure Race where
  time: Nat
  distance: Nat
deriving Repr

def findRoots (race: Race): Float × Float :=
  let time := race.time.toFloat
  let distance := race.distance.toFloat
  let t2minus4d := Float.sqrt $ time ^ 2 - 4 * distance
  let bottom := (time - t2minus4d) / 2.0
  let top := (time + t2minus4d) / 2.0
  ⟨ bottom, top ⟩

def Parsec.tag : Parsec String := do
  Parsec.manyChars (Parsec.satisfy $ λ c => c ≠ ':') <* Parsec.pchar ':' <* Parsec.ws

def Parsec.taggedNats : Parsec $ Array Nat := do
  let _tag ← Parsec.tag
  Parsec.many1 $ String.toNat! <$> Parsec.many1Chars Parsec.digit <* Parsec.ws

def Parsec.race : Parsec $ Array Race := do
  let times ← Parsec.taggedNats
  let distances ← Parsec.taggedNats
  return times.zipWith distances $ λ a b => ⟨ a, b ⟩

def puzzle1 : Except String Nat :=
  Array.map (between ∘ findRoots) <$> Parsec.race |>.run advent
  |>.map $ λ a => a.foldl Nat.mul 1

#eval puzzle1

def Parsec.allNats : Parsec Nat := do
  let _tag ← Parsec.tag
  String.toNat! <$> Parsec.many1Chars (Parsec.digit <* Parsec.ws)

def Parsec.raceV2 : Parsec Race := do
  return ⟨ ← Parsec.allNats, ← Parsec.allNats ⟩

def puzzle2 : Except String Nat :=
  (between ∘ findRoots) <$> Parsec.raceV2 |>.run advent

#eval puzzle2
