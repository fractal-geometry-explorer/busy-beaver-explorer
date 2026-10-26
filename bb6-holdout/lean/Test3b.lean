import BB6.Round
open BB6

instance : BEq MarkT := ⟨fun a b => decide (a = b)⟩
instance : BEq Mark := ⟨fun a b => a.t == b.t && a.p == b.p⟩

def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616

/-- A random well-formed round start: marks M, W, B with stripes of the right parity (possibly empty when the
parity allows), and a final stripe of the right parity. -/
def genState (seed : Nat) : List Mark × Nat := Id.run do
  let mut s := lcg (seed + 12345)
  let nm := (s / 65536) % 6
  let mut ms : List Mark := []
  let mut q := 4
  let mut u := false       -- value of the cell before q
  for _ in [0:nm] do
    s := lcg s
    let t : MarkT := match (s / 65536) % 3 with | 0 => .M | 1 => .W | _ => .B
    s := lcg s
    let base := (s / 65536) % 5
    -- stripe length parity: odd iff u = mval t
    let len := if u == mval t then 2 * base + 1 else 2 * base
    ms := ms ++ [⟨t, q + len⟩]
    q := q + len + mlen t
    u := mval t
  s := lcg s
  let base := (s / 65536) % 5
  let len := if u == false then 2 * base + 1 else 2 * base
  return (ms, q + len)

def showPR : PR' → String
  | .newRound ms W => s!"next W={W} {repr ms}"
  | .gap _ g _ W => s!"gap {g} W={W}"
  | .halt => "halt"
  | .uncovered => "uncovered"

structure Tally where
  agree : Nat := 0
  bothHalt : Nat := 0
  bothUnc : Nat := 0
  zUncOnly : Nat := 0
  lUncOnly : Nat := 0
  differ : Nat := 0
  samples : List String := []

/-- The simulator's trailing wall (a wall in the last two cells, one past the width) is no wall and width W − 1. -/
def canon (ms : List Mark) (W : Nat) : List Mark × Nat :=
  match ms.getLast? with
  | some m => if m.t == .W && m.p + 1 == W then (ms.dropLast, W - 1) else (ms, W)
  | none => (ms, W)

def classify (t : Tally) (ms : List Mark) (W : Nat) : Tally :=
  let z := roundZ 1000 [] 1 ms W
  let o := Model.round ⟨⟨.G, 1⟩ :: ms, W⟩
  let add (t : Tally) (msg : String) := if t.samples.length < 12 then { t with samples := t.samples ++ [msg] } else t
  match z, o with
  | .newRound ms' W', .next s =>
    let (cm, cW) := canon s.marks s.W
    if cm == (⟨.G, 1⟩ :: ms') && cW == W' then { t with agree := t.agree + 1 }
    else add { t with differ := t.differ + 1 } s!"DIFF start W={W} {repr ms}: zipper {showPR z}; list W={s.W} {repr s.marks}"
  | .halt, .halt => { t with bothHalt := t.bothHalt + 1 }
  | .uncovered, .uncovered _ => { t with bothUnc := t.bothUnc + 1 }
  | .uncovered, _ => add { t with zUncOnly := t.zUncOnly + 1 } s!"ZUNC start W={W} {repr ms}"
  | z, .uncovered why => add { t with lUncOnly := t.lUncOnly + 1 } s!"LUNC({why}) start W={W} {repr ms}: zipper {showPR z}"
  | z, _ => add { t with differ := t.differ + 1 } s!"DIFF2 start W={W} {repr ms}: zipper {showPR z}"

def runAll (n : Nat) : Tally := Id.run do
  let mut t : Tally := {}
  for i in [0:n] do
    let (ms, W) := genState i
    t := classify t ms W
  return t

#eval let t := runAll 20000
  s!"agree {t.agree}, both halt {t.bothHalt}, both uncovered {t.bothUnc}, zipper-only uncovered {t.zUncOnly}, list-only uncovered {t.lUncOnly}, differ {t.differ}\n" ++ String.intercalate "\n" t.samples
