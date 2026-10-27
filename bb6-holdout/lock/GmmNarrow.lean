import BB6.Round
open BB6

/-! # Two-marker states with the narrowest gaps, at every width (untrusted driver: statistics only)

Runs the proved round model `roundZ` from G 1, M m, M E − 2 for every odd width E up to `Emax` with the right gap
E − m equal to 5, 7, 9 or 11, and with the left gap m equal to 4, 6, 8 or 10, until the bare one-marker tape (or a
halt, `uncovered`, or 5000 rounds), and lists the widths that do not reach it.  (`GmmHalts.lean` scans every state
to width 16,001; the October 20 scan with the C mark model, `../csearch/gmmseg.c`, went to 262,143 but stopped at
m = E − 7.)

usage: lean --load-dynlib=cbuild/so/libBB6.so --run ../lock/GmmNarrow.lean 262143 -/

inductive Out where
  | clean | halt | uncov | long
instance : Inhabited Out := ⟨.long⟩

partial def go (R : Nat) : Nat → List Mark → Nat → Out
  | n, ms, W =>
    if n ≥ R then .long else
    match roundZ 100000000 [] 1 ms W with
    | .newRound ms' W' =>
      match ms' with
      | [e] => if e.t == .M && e.p + 2 == W' then .clean else go R (n + 1) ms' W'
      | _ => go R (n + 1) ms' W'
    | .halt => .halt
    | _ => .uncov

def main (args : List String) : IO Unit := do
  let Emax := (args.getD 0 "262143").toNat!
  for rg in [5, 7, 9, 11] do
    let mut c := 0; let mut bad : List Nat := []
    let mut E := rg + 4
    while E ≤ Emax do
      let m := E - rg
      if m ≥ 4 then
        match go 5000 0 [⟨.M, m⟩, ⟨.M, E - 2⟩] E with
        | .clean => c := c + 1
        | _ => bad := E :: bad
      E := E + 2
    IO.println s!"right gap {rg}: clean {c}, not clean at E = {bad.reverse.take 20}"
  for lg in [4, 6, 8, 10] do
    let mut c := 0; let mut bad : List Nat := []
    let mut E := lg + 5
    while E ≤ Emax do
      match go 5000 0 [⟨.M, lg⟩, ⟨.M, E - 2⟩] E with
      | .clean => c := c + 1
      | _ => bad := E :: bad
      E := E + 2
    IO.println s!"left gap {lg}: clean {c}, not clean at E = {bad.reverse.take 20}"
