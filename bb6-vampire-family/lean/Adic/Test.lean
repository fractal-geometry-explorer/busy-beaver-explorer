import Adic.Machines

/-!
# Tests of the 2-adic checker

* `halt_example`: the whole chain on a real halting E-event.  From context 43 of the table with n = 13,913, the core
  with F0 = 1LC meets a halting entry at pass 20; the checker finds it (3 segments of 8 passes, leaves of 4), so that
  configuration halts.  Evaluated by the kernel.
* `agree_*`: the checker's `solve` and the abstract map agree with the existing orbit `V*.oiter` (contexts and n,
  2^12 passes from each variant's start), and 2^k n_k = 3^k n + B_k holds for the B that `solve` returns.
-/

namespace Adic.Test

open Adic

theorem halt_seg : seg VLC.Adic.tab 8 4 3 (3 ^ 8) 3 43 [13913] = true := by decide +kernel

/-- **A halt proved through the checker**: the core with F0 = 1LC halts from the E-event (context 43, 13,913). -/
theorem halt_example : TM.Halts VLC.trans (Core.Ev (ctx 43) 13913) :=
  halts_of_seg (i := 43) (ds := [13913]) (N := 0) VLC.Adic.nextOK VLC.Adic.haltOK 8 4 3 3 (by decide)
    (by rw [show val 8 [13913] = 13913 from rfl]; exact Core.Reaches.refl _) (by decide) halt_seg

/-- The abstract map against the existing orbit. -/
def agree (t : Tab) (orb : Nat → Option (List Bool × Nat × Nat)) (i n K : Nat) : Bool :=
  match iter t K (i, n), orb K, solve t 16 30 true i n K with
  | some (j, m), some (c, m', _), .go j' B => ctx j == c && m == m' && j == j' && 2 ^ K * m == 3 ^ K * n + B
  | _, _, _ => false

theorem agree_VLC : agree VLC.Adic.tab (fun K => VLC.oiter K H121010.x0) 0 19 4096 = true := by native_decide
theorem agree_VLA : agree VLA.Adic.tab (fun K => VLA.oiter K H160156.x0) 1 15 4096 = true := by native_decide
theorem agree_VRB : agree VRB.Adic.tab (fun K => VRB.oiter K H82614.x0) 1 17 4096 = true := by native_decide

end Adic.Test
