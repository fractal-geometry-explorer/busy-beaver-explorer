import Block
import Period

/-! The end of the reach as a list configuration, and why it is `C 7` (kernel). -/

namespace H32641

open TM

/-- `C 7` as lists. -/
def finalF : FCfg St := ⟨[], false :: ((List.replicate 7 accb).flatten ++ X), .A⟩

theorem app_flatten_replicate (w : List Bool) (s : Tape) : ∀ k, app (List.replicate k w).flatten s = rep k w s := by
  intro k; induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, ← app_app, ih]; rfl

theorem finalF_ok : finalF.toCfg = C 7 := by
  simp only [finalF, FCfg.toCfg, C, app_cons, app_nil]
  rw [← app_app, app_flatten_replicate]

theorem sem_m0 : sem ⟨[], [], .A, true⟩ = init := rfl

end H32641
