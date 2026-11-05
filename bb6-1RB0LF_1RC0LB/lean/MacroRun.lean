import Macro

/-!
# The macro machine, run for many steps

`mrun t M0` is the macro machine after `t` steps from `M0` (the pass start after 12 machine steps), or `none` if it
got stuck on the way.  `mok t M` is the same check as a tail-recursive loop, so that compiled evaluation can run it
for a long time; `mok_iff` proves the two agree, by the kernel.  The bounded run itself is `native_decide`, so it
trusts Lean's compiler.
-/

namespace BB6e

open TM

/-- `true` iff the macro machine runs `t` steps from `M` without getting stuck. -/
def mok : Nat → MC → Bool
  | 0, _ => true
  | t + 1, M => match mstep M with
    | none => false
    | some M' => mok t M'

theorem mok_iff (t : Nat) : ∀ M, mok t M = true ↔ ∃ M', mrun t M = some M' := by
  induction t with
  | zero => intro M; simp [mok, mrun]
  | succ t ih =>
    intro M
    simp only [mok, mrun]
    cases h : mstep M with
    | none => simp
    | some M' => simpa using ih M'

/-- The macro machine does not get stuck in its first 10⁸ steps from `M0` (compiled evaluation). -/
theorem macro_runs_100M : ∃ M, mrun 100000000 M0 = some M :=
  (mok_iff _ _).1 (by native_decide)

/-- Hence the machine runs at least 10⁸ steps from blank tape without halting (each macro step is at least one machine
step; the true count is far larger). -/
theorem blank_runs_macro_100M : ∃ n c, 100000000 ≤ n ∧ steps n init = some c := by
  obtain ⟨M, hM⟩ := macro_runs_100M
  obtain ⟨k, hk, hs⟩ := mrun_sound _ M0 M hM
  exact ⟨12 + k, _, by omega, steps_seq trans blank_to_M0 hs⟩

end BB6e
