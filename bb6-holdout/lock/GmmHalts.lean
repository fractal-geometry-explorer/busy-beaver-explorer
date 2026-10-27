import BB6.Round
open BB6

/-! # Which two-marker states halt (untrusted driver: statistics only)

Runs the proved round model `roundZ` (`../lean/BB6/Round.lean`, the model of `round_run`) from every two-marker state
G 1, M m, M E − 2 (m even, E odd, both gaps m and E − m at least `g0`) with E in a range, round by round, until the
run reaches the bare one-marker tape (a clean tape), halts, or leaves the model (`uncovered`), or `R` rounds pass.
It counts the outcomes and prints the halting starts with the shapes of their round starts.

usage: lean --load-dynlib=cbuild/so/libBB6.so --run ../lock/GmmHalts.lean Emin Emax g0 R [show] -/

def tch : MarkT → Char | .G => 'G' | .M => 'M' | .W => 'W' | .B => 'B'
def shp (ms : List Mark) : String := String.ofList (ms.map (fun m => tch m.t))

inductive Out where
  | clean (n : Nat) (W : Nat) (rets : Nat) (walls3 : Bool)
  | halt (n : Nat) (hist : List String)
  | uncov (n : Nat) (hist : List String)
  | long

instance : Inhabited Out := ⟨.long⟩

/-- `rets` counts returns to two markers, `w3` whether a round start with three or more walls was met. -/
partial def go (R : Nat) : Nat → List Mark → Nat → Nat → Bool → List String → Out
  | n, ms, W, rets, w3, hist =>
    if n ≥ R then .long else
    match roundZ 1000000 [] 1 ms W with
    | .newRound ms' W' =>
      let h := s!"{shp ms'}" :: hist
      let w3' := w3 || (ms'.filter (fun m => m.t == .W)).length ≥ 3
      match ms' with
      | [e] => if e.t == .M && e.p + 2 == W' then .clean (n + 1) W' rets w3' else go R (n + 1) ms' W' rets w3' h
      | [a, e] =>
        if a.t == .M && e.t == .M && e.p + 2 == W' then go R (n + 1) ms' W' (rets + 1) w3' h
        else go R (n + 1) ms' W' rets w3' h
      | _ => go R (n + 1) ms' W' rets w3' h
    | .halt => .halt n hist
    | _ => .uncov n hist

def main (args : List String) : IO Unit := do
  let Emin := (args.getD 0 "101").toNat!
  let Emax := (args.getD 1 "1001").toNat!
  let g0 := (args.getD 2 "8").toNat!
  let R := (args.getD 3 "400").toNat!
  let nshow := (args.getD 4 "20").toNat!
  let mut nClean := 0
  let mut nHalt := 0
  let mut nUnc := 0
  let mut nLong := 0
  let mut nW3 := 0
  let mut shown := 0
  let mut hW3 := 0
  let mut maxN := 0
  let mut maxRets := 0
  let mut E := if Emin % 2 == 1 then Emin else Emin + 1
  while E ≤ Emax do
    let mut m := g0 + g0 % 2
    while m + g0 ≤ E do
      match go R 0 [⟨.M, m⟩, ⟨.M, E - 2⟩] E 0 false ["MM"] with
      | .clean n _ rets w3 =>
        nClean := nClean + 1
        if w3 then nW3 := nW3 + 1
        maxN := max maxN n
        maxRets := max maxRets rets
      | .halt n hist =>
        nHalt := nHalt + 1
        if hist.any (fun s => (s.toList.filter (· == 'W')).length ≥ 3) then hW3 := hW3 + 1
        if shown < nshow then
          shown := shown + 1
          IO.println s!"halt: m = {m}, E = {E} after {n} rounds: {".".intercalate hist.reverse}"
      | .uncov n hist =>
        nUnc := nUnc + 1
        if shown < nshow then
          shown := shown + 1
          IO.println s!"uncovered: m = {m}, E = {E} after {n} rounds: {".".intercalate hist.reverse}"
      | .long => nLong := nLong + 1
      m := m + 2
    E := E + 2
  IO.println s!"E in [{Emin}, {Emax}], gaps ≥ {g0}: clean {nClean} (of which met three walls {nW3}), halt {nHalt} (met three walls {hW3}), uncovered {nUnc}, over {R} rounds {nLong}; most rounds to the one-marker tape {maxN}, most returns to two markers on the way {maxRets}"
