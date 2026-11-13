import Machine

/-!
# A tape of the counter's shape that halts

The tape `D> 0 (010)^4 0001 (001)^2 01` (gap list 2^4 r 2^2 END: first block 4, one digit r, a block of 2, END) has
exactly the shape of the counter's configurations, and the machine halts from it after 234,048 steps: the digits
run into END and wreck it.  So no proof of non-halting can rest on the shape alone; it has to keep track of the
block lengths.  (Evaluated by compiled code, `native_decide`.)
-/

namespace H83770

open TM

theorem halts_of_fsteps (c : FCfg St) (n : Nat)
    (h : (match TM.fsteps trans n c with | some c' => (TM.fstep trans c').isNone | none => false) = true) :
    Halts trans c.toCfg := by
  cases e : TM.fsteps trans n c with
  | none => simp [e] at h
  | some c' =>
    simp only [e] at h
    refine ⟨n, c'.toCfg, ?_, ?_⟩
    · rw [FCfg.steps_eq, e]; rfl
    · rw [FCfg.step_eq]
      cases h' : TM.fstep trans c' with
      | none => rfl
      | some _ => simp [h'] at h

/-- The tape 2^4 r 2^2 END, head in state D at its left end. -/
def ex : FCfg St := ⟨[], [false, false, true, false, false, true, false, false, true, false, false, true, false, false,
  false, false, true, false, false, true, false, false, true, false, true], .D⟩

theorem ex_halts : Halts trans ex.toCfg :=
  halts_of_fsteps ex 234048 (by native_decide)

end H83770
