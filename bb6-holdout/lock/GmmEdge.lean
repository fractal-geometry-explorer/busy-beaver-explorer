import BB6.Round
open BB6

/-! # Two-marker states at the edges, for large widths (untrusted driver: statistics only)

Runs the proved round model `roundZ` from G 1, M m, M E − 2 where one gap is small and the width is large: the
marker near the gap (m = c) or near the end (E − m = c + 1), for c in [cmin, cmax] (even) and E running over `cnt`
odd values spread over [E0, E0 + span).  Each run goes until the bare one-marker tape, a halt, `uncovered`, or
`R` rounds.

usage: lean --load-dynlib=cbuild/so/libBB6.so --run ../lock/GmmEdge.lean cmin cmax E0 span cnt R -/

inductive Out where
  | clean (n : Nat)
  | halt (n : Nat)
  | uncov (n : Nat)
  | long

instance : Inhabited Out := ⟨.long⟩

partial def go (R : Nat) : Nat → List Mark → Nat → Out
  | n, ms, W =>
    if n ≥ R then .long else
    match roundZ 100000000 [] 1 ms W with
    | .newRound ms' W' =>
      match ms' with
      | [e] => if e.t == .M && e.p + 2 == W' then .clean (n + 1) else go R (n + 1) ms' W'
      | _ => go R (n + 1) ms' W'
    | .halt => .halt n
    | _ => .uncov n

def main (args : List String) : IO Unit := do
  let cmin := (args.getD 0 "4").toNat!
  let cmax := (args.getD 1 "64").toNat!
  let E0 := (args.getD 2 "1000001").toNat!
  let span := (args.getD 3 "1000000").toNat!
  let cnt := (args.getD 4 "1000").toNat!
  let R := (args.getD 5 "5000").toNat!
  let mut st : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0]
  let mut maxr := 0
  for side in [0, 1] do
    let mut c := cmin
    while c ≤ cmax do
      for i in List.range cnt do
        -- an odd width, spread over the span by a fixed multiplier
        let E := E0 + 2 * ((i * 7919 * 104729) % (span / 2))
        let E := if E % 2 == 1 then E else E + 1
        let m := if side == 0 then c else E - (c + 1)
        let r := go R 0 [⟨.M, m⟩, ⟨.M, E - 2⟩] E
        match r with
        | .clean n => st := st.modify (4 * side) (· + 1); maxr := max maxr n
        | .halt n => st := st.modify (4 * side + 1) (· + 1); IO.println s!"halt: m = {m}, E = {E} after {n} rounds"
        | .uncov n => st := st.modify (4 * side + 2) (· + 1); IO.println s!"uncovered: m = {m}, E = {E} after {n} rounds"
        | .long => st := st.modify (4 * side + 3) (· + 1); IO.println s!"long: m = {m}, E = {E}"
      c := c + 2
  IO.println s!"marker near the gap: clean {st[0]!}, halt {st[1]!}, uncovered {st[2]!}, over {R} rounds {st[3]!}"
  IO.println s!"marker near the end: clean {st[4]!}, halt {st[5]!}, uncovered {st[6]!}, over {R} rounds {st[7]!}"
  IO.println s!"most rounds to the one-marker tape: {maxr}"
