import Tabs

/-!
Compiled benchmark of the 2-adic checker: the pieces `seg` is made of (`solve`, `low`, `mulAdd`, `shr`), with the
final state returned so that it can be compared with `c/orbit.c ... check K`.

usage: bench V I N L S [LF]   (V = LC, LA or RB; from context number I with n = N, S segments of L passes, leaves
of LF passes, default 24).  Prints the final context number, n mod 2^64, its bit length and the time.
-/

open Adic

def segS (t : Tab) (L Lf f m : Nat) : Nat → Nat → List Nat → Nat → (String × Nat × List Nat)
  | 0, c, ds, _ => ("no halt", c, ds)
  | s + 1, c, ds, done =>
    match solve t Lf f true c (low L ds) L with
    | .halt => (s!"halt in segment {done}", c, ds)
    | .go c' B =>
      match shr L (mulAdd L m ds B) with
      | some es => segS t L Lf f m s c' es (done + 1)
      | none => ("shr failed", c, ds)
    | .out => (s!"out of the table in segment {done}", c, ds)

def main (args : List String) : IO Unit := do
  let v := args[0]!
  let i := args[1]!.toNat!
  let n := args[2]!.toNat!
  let L := args[3]!.toNat!
  let s := args[4]!.toNat!
  let Lf := (args[5]?.getD "24").toNat!
  let t := if v == "LC" then tLC else if v == "LA" then tLA else tRB
  let t0 ← IO.monoMsNow
  let (msg, c, ds) := segS t L Lf 64 (3 ^ L) s i [n] 0
  let N := val L ds
  let t1 ← IO.monoMsNow
  IO.println s!"{msg}: {s} segments of {L} passes ({s * L} passes), context {c}, n mod 2^64 = {N % 2 ^ 64}, bits {N.log2 + 1}, {t1 - t0} ms"
