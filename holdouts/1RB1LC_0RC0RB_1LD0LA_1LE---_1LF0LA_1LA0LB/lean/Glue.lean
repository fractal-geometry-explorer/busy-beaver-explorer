import Machine

/-! Re-bracketing a repeat into a repeat of a power of its word (used by the passes `py/symglue.py` writes). -/

namespace H49767

open TM

theorem rep_eq_app (w : List Bool) : ∀ (k : Nat) (s : Tape), rep k w s = app (List.replicate k w).flatten s
  | 0, _ => rfl
  | k + 1, s => by rw [rep_succ, rep_eq_app w k s, app_app]; simp [List.replicate_succ, List.flatten_cons]

theorem rep_mul_word (k n : Nat) (w : List Bool) (s : Tape) :
    rep (k * n) w s = rep n (List.replicate k w).flatten s := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, Nat.add_comm, rep_add, ih, rep_succ, rep_eq_app]

end H49767
