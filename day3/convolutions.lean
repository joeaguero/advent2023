universe u v

theorem Nat.lt_gt {a b: Nat} : (a > b) = (b < a) := by rfl
theorem Nat.sub_one {n : Nat} : n - 1 = n.pred := by rfl

theorem Fin.n_gt_zero {n: Nat} (idx: Fin n) : n > 0 := by
  cases n with
  | zero => exact Fin.elim0 idx
  | succ n => rw [Nat.lt_gt]; simp [Nat.succ_pos]

def Fin.incr {n : Nat} (i : Fin n) : Fin n :=
  let newVal := (i.val + 1) % n
  Fin.ofNat' newVal $ Fin.n_gt_zero i

def Fin.decr {n : Nat} (i : Fin n) : Fin n :=
  let newVal := (i.val - 1) % n
  Fin.ofNat' newVal $ Fin.n_gt_zero i

def parseNatCharsL (arr: Array Char) (pos: Fin arr.size) (acc: List Char) : List Char :=
  let char := arr.get pos
  if char.isDigit then
    let acc' := char :: acc
    if _h: pos.val ≤ 0 then acc'
    else parseNatCharsL arr pos.decr acc'
  else acc

  termination_by parseNatCharsL arr pos acc => pos.val
  decreasing_by {
    have bound : pos.val < arr.size := by
      apply Fin.val_lt_of_le
      apply Nat.le_refl
    simp_wf
    unfold Fin.decr
    simp
    unfold Fin.ofNat'
    simp
    cases val: pos.val with
    | zero =>
      rw [←Nat.not_gt_eq, val] at _h
      contradiction
    | succ n =>
      rw [Nat.sub_one, Nat.pred_succ]
      rw [val] at bound
      have n_in_bound : n < arr.size := by
        apply Nat.lt_of_succ_lt bound
      rw [Nat.mod_eq_of_lt n_in_bound]
      rw [Nat.mod_eq_of_lt n_in_bound]
      apply Nat.lt_succ_self
  }

def parseNatCharsR (arr: Array Char) (pos: Fin arr.size) (acc: List Char) : List Char :=
  let char := arr.get pos
  if char.isDigit then
    let acc' := acc ++ [char]
    if _h: pos.val + 1 < arr.size then
      parseNatCharsR arr pos.incr acc'
    else acc'
  else acc

  termination_by parseNatCharsR arr pos acc => arr.size - pos.val
  decreasing_by {
    simp_wf
    unfold Fin.incr
    simp
    unfold Fin.ofNat'
    simp
    cases val: pos.val with
    | zero =>
      rw [val] at _h
      simp at _h
      simp
      repeat rw [Nat.mod_eq_of_lt _h]
      apply Nat.sub_lt (Fin.n_gt_zero pos) (Nat.zero_lt_one)
    | succ n =>
      rw [val] at _h
      repeat rw [Nat.mod_eq_of_lt _h]

      apply Nat.sub_succ_lt_self
      rw [Nat.add_succ] at _h
      simp at _h
      apply Nat.lt_of_succ_lt
      exact _h
  }

def parseNat (arr: Array Char) (pos: Fin arr.size) : Option Nat :=
  let char := arr.get pos
  if char.isDigit then
    let lhs: List Char :=
      if pos.val ≤ 0 then []
      else parseNatCharsL arr pos.decr []
    let rhs: List Char :=
      if pos.val + 1 ≥ arr.size then []
      else parseNatCharsR arr pos.incr []
    lhs ++ char :: rhs |>.asString.toNat?
  else none

def parseNatR (arr: Array Char) (pos: Fin arr.size) : Option Nat :=
  if pos.val = 0 then none
  else
    let char := arr.get pos
    if char.isDigit then
      let rhs: List Char :=
        if pos.val + 1 ≥ arr.size then []
        else parseNatCharsR arr pos.incr []
      char :: rhs |>.asString.toNat?
    else none

def parseNatL (arr: Array Char) (pos: Fin arr.size) : Option Nat :=
  if pos.val + 1 >= arr.size then none
  else
    let char := arr.get pos
    if char.isDigit then
      let lhs: List Char :=
        if pos.val ≤ 0 then []
        else parseNatCharsL arr pos.decr []
      lhs ++ [char] |>.asString.toNat?
    else none

def parseGearRatios (arr: Array (Array Char)) :=
  arr.mapIdx $ λ i r ↦
    let vals := r.mapIdx $ λ j c ↦
      let digits : Array (Option Nat) := #[]
      if c == '*' then
        let digits := digits.push $ parseNatL r j.decr
        let digits := digits.push $ parseNatR r j.incr
        let digits := if i.val = 0 then digits
          else let row_up := arr.get i.decr
            if h₁: row_up.size = r.size then
              have proof: j.val < row_up.size := by
                rw [h₁]
                exact j.2
              let up_ind: Fin row_up.size := { val:= j.val, isLt:= proof }
              let val := parseNat row_up up_ind
              match val with
              | some n => digits.push n
              | none => (digits.push $ parseNatL row_up up_ind.decr) |>.push $ parseNatR row_up up_ind.incr
            else digits
        let digits := if i.val + 1 = arr.size then digits
          else let row_down := arr.get i.incr
            if h₂: row_down.size = r.size then
              have proof: j.val < row_down.size := by
                rw [h₂]
                exact j.2
              let down_ind : Fin row_down.size := { val:=j.val, isLt:= proof }
              let val := parseNat row_down down_ind
              match val with
              | some n => digits.push n
              | none => (digits.push $ parseNatL row_down down_ind.decr) |>.push $ parseNatR row_down down_ind.incr
            else digits
        let digits := Array.filter Option.isSome digits
        if digits.size = 2 then
          let lhs := digits.get! 0 |>.getD 0
          let rhs := digits.get! 1 |>.getD 0
          lhs * rhs
        else 0
      else 0
    vals.foldl Nat.add 0

def parseGearRatio (arr: Array (Array Char)) : Nat :=
  parseGearRatios arr |>.foldl Nat.add 0

partial def accEngine (acc: Array (Array Char)) (stream: IO.FS.Stream) : IO (Array (Array Char)) := do
  let line ← stream.getLine
  if line.isEmpty then pure acc else
    accEngine (acc.push line.toList.toArray) stream

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
    let acc' := parseGearRatio arr
    handleIO acc' exitCode args
  | filename :: args =>
    let stream ← fileStream filename
    match stream with
    | none => handleIO acc 2 args
    | some stream =>
      let arr ← accEngine [].toArray stream
      let acc' := parseGearRatio arr
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

