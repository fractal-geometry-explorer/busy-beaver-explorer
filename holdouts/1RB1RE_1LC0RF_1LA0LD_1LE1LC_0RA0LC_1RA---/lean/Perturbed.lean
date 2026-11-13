import Machine

/-!
# Counter configurations that halt

The run from blank tape only ever shows the counter tapes `C> a^n0 s(d1) a^n1 ... s(dk) a^nk 01` (`a = 001`,
`s(0)=0, s(1)=011, s(2)=00, s(3)=0101`) and a few short irregular patterns.  The tapes below have exactly that
form, but with *small timers* (short blocks): from them the machine halts.  So nonhalting from blank tape cannot
follow from the sweep rules and the shape of the tape alone; it depends on the values the blocks take in the
actual run (the timers never run out together).  Found with `py/perturb.py`, checked with two simulators.
-/

namespace H175626

open TM

/-- `a = 001`. -/
def wa : List Bool := [false, false, true]
/-- The separators `s(d)`. -/
def sep : Nat → List Bool
  | 0 => [false]
  | 1 => [false, true, true]
  | 2 => [false, false]
  | _ => [false, true, false, true]

/-- `C> a^n0 s(d1) a^n1 ... s(dk) a^nk 01`, the head on the first cell of `a^n0`. -/
def counter (n0 : Nat) (ds : List (Nat × Nat)) : FCfg St :=
  ⟨[], (List.replicate n0 wa).flatten ++ (ds.map fun (d, n) => sep d ++ (List.replicate n wa).flatten).flatten
      ++ [false, true], .C⟩

/-- Halting read off a bounded evaluation: the run of `n` steps exists and the next step halts. -/
theorem halts_of_eval (c0 : FCfg St) (n : Nat)
    (h : (match fsteps n c0 with | some c => (fstep c).isNone | none => false) = true) :
    TM.Halts trans c0.toCfg := by
  cases e : fsteps n c0 with
  | none => rw [e] at h; cases h
  | some c =>
    rw [e] at h
    refine ⟨n, c.toCfg, ?_, ?_⟩
    · show TM.steps trans n c0.toCfg = _
      rw [FCfg.steps_eq]; show Option.map _ (TM.fsteps trans n c0) = _; rw [show TM.fsteps trans n c0 = some c from e]; rfl
    · show TM.step trans c.toCfg = none
      rw [FCfg.step_eq]
      cases hc : TM.fstep trans c with
      | none => rfl
      | some c' => exact absurd h (by show ¬ ((TM.fstep trans c).isNone = true); rw [hc]; simp)

/-- `C> a^2 0 a^4 01` (one digit, 0, with block 4) halts: step 309,457 is the halting transition F1. -/
theorem counter_2_0_halts : TM.Halts trans (counter 2 [(0, 4)]).toCfg :=
  halts_of_eval _ 309456 (by native_decide)

/-- `C> a^43 0101 a^4 0101 a^4 01` (counter value 15, both digits 3, blocks 4 and 4) halts: step 4,905,443 is the
halting transition F1. -/
theorem counter_43_33_halts : TM.Halts trans (counter 43 [(3, 4), (3, 4)]).toCfg :=
  halts_of_eval _ 4905442 (by native_decide)

end H175626
