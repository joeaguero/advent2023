import Lean.Data.HashMap
import Lean.Data.Parsec
open Lean

universe u

instance {α : Type u} [comparison: Ord α] : Ord (Array α) where
  compare xs ys := Id.run do
    let pair := xs.zip ys
    let mut result := Ordering.eq

    for (x, y) in pair do
      match comparison.compare x y with
      | Ordering.lt =>
        result := Ordering.lt
        break
      | Ordering.gt =>
        result := Ordering.gt
        break
      | Ordering.eq => continue

    match result with
    | Ordering.eq => return Ord.compare xs.size ys.size
    | _ => return result

inductive Card : Type where
  | C2 : Card | C3 : Card | C4 : Card | C5 : Card
  | C6 : Card | C7 : Card | C8 : Card | C9 : Card
  | CT : Card | CJ : Card | CQ : Card | CK : Card
  | CA : Card
deriving Repr, Ord, Hashable, BEq

inductive Card2 : Type where
  | CJ | C2 | C3 | C4
  | C5 | C6 | C7 | C8
  | C9 | CT | CQ | CK
  | CA
deriving Repr, Ord, Hashable, BEq

inductive Hand : Type where
  | HighCard : Hand | OnePair : Hand | TwoPair : Hand
  | ThreeOfAKind: Hand | FullHouse : Hand | FourOfAKind : Hand
  | FiveOfAKind : Hand
deriving Repr, Ord

def toSorted {α : Type} [BEq α] [Hashable α] (counter: HashMap α Nat): List Nat :=
  counter.toArray.map Prod.snd |>.insertionSort (· ≥ ·) |>.toList

def toHand2 (hand : { arr: Array Card2 // arr.size = 5 }): Hand := Id.run do
  let mut counter : HashMap Card2 Nat := HashMap.empty

  for card in hand.val do
    match counter.find? card with
    | none => counter := counter.insert card 1
    | some n => counter := counter.insert card n.succ

  match counter.find? Card2.CJ with
  | none =>
    match toSorted counter with -- no joker
    | [5] => .FiveOfAKind
    | 4 :: _ => .FourOfAKind
    | [3, 2] => .FullHouse
    | 3 :: _ => .ThreeOfAKind
    | 2 :: 2 :: _ => .TwoPair
    | 2 :: _ => .OnePair
    | _ => .HighCard

  | some n =>
    counter := counter.erase Card2.CJ
    -- match on all minus joker
    match n with
    | 1 =>
      match toSorted counter with
      | [4] => .FiveOfAKind
      | 3 :: _ => .FourOfAKind
      | [2, 2] => .FullHouse
      | 2 :: _ => .ThreeOfAKind
      | _ => .OnePair
    | 2 =>
      match toSorted counter with
      | [3] => .FiveOfAKind
      | 2 :: _ => .FourOfAKind
      | _ => .ThreeOfAKind
    | 3 =>
      match toSorted counter with
      | [2] => .FiveOfAKind
      | _ => .FourOfAKind
    | 4 => .FiveOfAKind
    | 5 => .FiveOfAKind
    | _ => .HighCard

def toHand (hand : {arr: Array Card // arr.size = 5}) : Hand := Id.run do
  let mut result : HashMap Card Nat := HashMap.empty

  for card in hand.val do
    match result.find? card with
    | none => result := result.insert card 1
    | some n => result := result.insert card n.succ

  match (result.toArray.map Prod.snd |>.insertionSort (· ≥ ·) |>.toList) with
  | [5] => .FiveOfAKind
  | 4 :: _ => .FourOfAKind
  | [3, 2] => .FullHouse
  | 3 :: _ => .ThreeOfAKind
  | 2 :: 2 :: _ => .TwoPair
  | 2 :: _ => .OnePair
  | _ => .HighCard

def compareHand2 (lhs rhs : {arr: Array Card2 // arr.size = 5}) : Ordering :=
  match Ord.compare (toHand2 lhs) (toHand2 rhs) with
  | Ordering.lt => Ordering.lt
  | Ordering.gt => Ordering.gt
  | Ordering.eq => Ord.compare lhs.val rhs.val

def compareHand (lhs rhs : {arr: Array Card // arr.size = 5}) : Ordering :=
  match Ord.compare (toHand lhs) (toHand rhs) with
  | Ordering.lt => Ordering.lt
  | Ordering.gt => Ordering.gt
  | Ordering.eq => Ord.compare lhs.val rhs.val

structure Bid where
  cards : { arr: Array Card // arr.size = 5 }
  points : Nat
deriving Repr

instance : Ord Bid where
  compare lhs rhs := compareHand lhs.cards rhs.cards

structure Bid2 where
  cards : { arr: Array Card2 // arr.size = 5 }
  points : Nat
deriving Repr

instance : Ord Bid2 where
  compare lhs rhs := compareHand2 lhs.cards rhs.cards

def Parsec.card2 : Parsec Card2 := do
  let char ← Parsec.anyChar
  match char with
  | 'A' => return .CA
  | 'K' => return .CK
  | 'Q' => return .CQ
  | 'J' => return .CJ
  | 'T' => return .CT
  | '2' => return .C2
  | '3' => return .C3
  | '4' => return .C4
  | '5' => return .C5
  | '6' => return .C6
  | '7' => return .C7
  | '8' => return .C8
  | '9' => return .C9
  | _ => Parsec.fail s!"invalid card: {char}"

def Parsec.hand2 : Parsec { arr: Array Card2 // arr.size = 5 } := do
  let c1 ← Parsec.card2
  let c2 ← Parsec.card2
  let c3 ← Parsec.card2
  let c4 ← Parsec.card2
  let c5 ← Parsec.card2
  return ⟨#[c1, c2, c3, c4, c5], by rfl⟩

def Parsec.card : Parsec Card := do
  let char ← Parsec.anyChar
  match char with
  | 'A' => return .CA
  | 'K' => return .CK
  | 'Q' => return .CQ
  | 'J' => return .CJ
  | 'T' => return .CT
  | '2' => return .C2
  | '3' => return .C3
  | '4' => return .C4
  | '5' => return .C5
  | '6' => return .C6
  | '7' => return .C7
  | '8' => return .C8
  | '9' => return .C9
  | _ => Parsec.fail s!"invalid card: {char}"

def Parsec.hand : Parsec { arr: Array Card // arr.size = 5 } := do
  let c1 ← Parsec.card
  let c2 ← Parsec.card
  let c3 ← Parsec.card
  let c4 ← Parsec.card
  let c5 ← Parsec.card
  return ⟨#[c1, c2, c3, c4, c5], by rfl⟩

def Parsec.nat : Parsec Nat := do
  let digits ← Parsec.many1Chars Parsec.digit
  return digits.toNat!

def Parsec.bid : Parsec Bid := do
  Bid.mk <$> Parsec.hand <*> (Parsec.ws *> Parsec.nat)

def Parsec.bid2 : Parsec Bid2 := do
  Bid2.mk <$> Parsec.hand2 <*> (Parsec.ws *> Parsec.nat)

def Bids.qsort {α : Type u } [Ord α] (bids: Array α): Array α :=
  bids.qsort $ λ lhs rhs => if let Ordering.gt := Ord.compare rhs lhs then true else false

def Parsec.bids : Parsec $ Array Bid := do
  let mut bids ← Parsec.many1 (Parsec.bid <* Parsec.ws)
  return Bids.qsort bids

def Parsec.bids2 : Parsec $ Array Bid2 := do
  let mut bids ← Parsec.many1 (Parsec.bid2 <* Parsec.ws)
  return Bids.qsort bids

def Parsec.winnings : Parsec Nat := do
  let bids ← Parsec.bids
  return (bids.mapIdx $ λ idx bid => idx.val.succ * bid.points) |>.foldl Nat.add 0

def Parsec.winnings2 : Parsec Nat := do
  let bids ← Parsec.bids2
  return (bids.mapIdx $ λ idx bid => idx.val.succ * bid.points) |>.foldl Nat.add 0

def Parsec.fromBids (bids: Array Bid) : Nat := Id.run do
  let mut bids : Array Bid := Bids.qsort bids
  return (bids.mapIdx $ λ idx bid => idx.val.succ * bid.points) |>.foldl Nat.add 0

partial def accumulate (str: String) (stream: IO.FS.Stream) : IO String := do
  let line ← stream.getLine
  if line.isEmpty then return str
  accumulate (str ++ line) stream

def fileStream (filename: System.FilePath) : IO (Option IO.FS.Stream) := do
  let fileExists ← filename.pathExists
  if not fileExists then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found {filename}"
    return none

  let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
  return some $ IO.FS.Stream.ofHandle handle

def handleSum (p: Parsec Nat) (acc: Nat) (exitCode: UInt32) (args: List String) : IO UInt32 := do
  match args with
  | [] =>
    println! s!"Result: {acc}"
    return exitCode
  | "-" :: args =>
    let stdin ← IO.getStdin
    let acc' ← accumulate "" stdin
    match p.run acc' with
    | .ok result => handleSum p (acc + result) exitCode args
    | .error err =>
      println! s!"Error: {err}"
      return exitCode
  | filename :: args =>
    let stream ← fileStream filename
    match stream with
    | none => handleSum p acc 2 args
    | some stream =>
      let acc' ← accumulate "" stream
      match p.run acc' with
      | .ok result => handleSum p (acc + result) exitCode args
      | .error err =>
        println! s!"Error: {err}"
        return exitCode

def main : List String → IO UInt32
  | [] => handleSum Parsec.winnings2 0 0 ["-"]
  | version :: args =>
    let args' := match args with
    | [] => ["-"]
    | _ => args
    match version with
    | "V1" => handleSum Parsec.winnings 0 0 args'
    | "V2" => handleSum Parsec.winnings2 0 0 args'
    | _ => handleSum Parsec.winnings2 0 0 (version :: args)

def advent: String :=
"KTJJT 220
QQQJA 483
32T3K 765
KK677 28
T55J5 684"

