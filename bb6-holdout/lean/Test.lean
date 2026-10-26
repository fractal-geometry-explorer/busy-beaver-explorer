import BB6.Model
open BB6

/-- A round start: state E, head on cell 3, left stream `0 0 1` then zeros (checked out to 60 cells). -/
def roundStartLike (c : Cfg) : Bool :=
  c.st == .E && c.r 0 == false && c.l 0 == false && c.l 1 == false && c.l 2 == true &&
  (List.range 60).all (fun i => c.l (i + 3) == false)

instance : BEq St := ⟨fun a b => decide (a = b)⟩

/-- Flatten the streams (which accumulate one closure per step) into lists of the first cells. -/
def normalize (c : Cfg) (nl nr : Nat) : Cfg :=
  let al := (List.range nl).toArray.map c.l
  let ar := (List.range nr).toArray.map c.r
  ⟨fun n => al.getD n false, fun n => ar.getD n false, c.st⟩

/-- Step the machine until the next round start; returns the step count and the configuration.  The streams are
flattened every 64 steps out to `width` cells (the tape is blank beyond). -/
def nextStart (fuel : Nat) (c : Cfg) (n0 : Nat) (width : Nat) : Option (Nat × Cfg) := Id.run do
  let mut cur := c
  for i in [0:fuel] do
    match step cur with
    | none => return none
    | some c' =>
      cur := if i % 64 == 63 then normalize c' width width else c'
      if roundStartLike cur then return some (n0 + i + 1, cur)
  return none

/-- Compare the model's round with the machine's, `rounds` times, from a mark state. -/
def compare (rounds : Nat) (s : MState) (c : Cfg) (acc : List (Nat × Bool × Nat × Nat)) : List (Nat × Bool × Nat × Nat) :=
  match rounds with
  | 0 => acc.reverse
  | r + 1 =>
    match Model.round s, nextStart 2000000 c 0 (s.W + 64) with
    | .next s', some (n, c') =>
      let ok := cellsOfStart (cfgOf s') (s'.W + 8) == cellsOfStart c' (s'.W + 8)
      compare r s' (normalize c' 4 (s'.W + 8)) ((n, ok, s'.W, s'.marks.length) :: acc)
    | _, _ => acc.reverse

def s0 : MState := ⟨[⟨.G, 1⟩], 5⟩
#eval cellsOfStart (cfgOf s0) 12
#eval (steps 17 ⟨blank, blank, .A⟩).map (fun c => cellsOfStart c 12)
def report (rs : List (Nat × Bool × Nat × Nat)) : String :=
  s!"rounds {rs.length}; mismatches {(rs.filter (fun x => !x.2.1)).length}; machine steps {(rs.map (fun x => x.1)).foldl (· + ·) 0}; final W {match rs.getLast? with | some x => x.2.2.1 | none => 0}"
#eval report (compare 200 s0 (cfgOf s0) [])

/-! Round starts whose last mark is a block, with the canonical width (an even stripe after the block, so the cell
W − 1 is a 1): the gap meets the block and the shift reaches blank tape (the BLOCK→blank row). -/
def s1 : MState := ⟨[⟨.G, 1⟩, ⟨.B, 8⟩], 13⟩
#eval cellsOfStart (cfgOf s1) 16
#eval Model.round s1
#eval report (compare 12 s1 (cfgOf s1) [])
def s2 : MState := ⟨[⟨.G, 1⟩, ⟨.M, 6⟩, ⟨.B, 12⟩], 19⟩
#eval compare 12 s2 (cfgOf s2) []
