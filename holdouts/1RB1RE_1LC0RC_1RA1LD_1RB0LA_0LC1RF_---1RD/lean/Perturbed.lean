import Machine

/-!
# Counter configurations that halt

At the left end the run from blank tape shows the tapes `D> 0 b (ba)^n1 s1 (ba)^n2 s2 ... (ba)^nk sk 1^4` (`a = 10`,
`b = 1110`, separators `s` in `a, b, ab, bb`, the base-4 digits 0..3).  The tapes below have exactly that form,
with short blocks; from them the machine halts.  So nonhalting from blank tape cannot follow from the digit rules
and the shape of the tape alone: it depends on the block lengths the actual run produces.  Found by
`py/perturb.py`, checked with two simulators.
-/

namespace H44531

open TM

def wa : List Bool := [true, false]
def wb : List Bool := [true, true, true, false]
/-- The separators, as base-4 digits: `a, b, ab, bb`. -/
def sep : Nat → List Bool
  | 0 => wa
  | 1 => wb
  | 2 => wa ++ wb
  | _ => wb ++ wb

/-- `D> 0 b (ba)^n1 s(d1) (ba)^n2 s(d2) ... 1^4`, the head on the leading 0: `n1` and then (digit, next block)
pairs, the last digit followed by `1^4`. -/
def counter (n1 : Nat) (ds : List (Nat × Nat)) (last : Nat) : FCfg St :=
  ⟨[], [false] ++ wb ++ (List.replicate n1 (wb ++ wa)).flatten
      ++ (ds.map fun (d, n) => sep d ++ (List.replicate n (wb ++ wa)).flatten).flatten
      ++ sep last ++ [true, true, true, true], .D⟩

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

/-- `D> 0 b (ba)^3 a (ba)^3 a 1^4` (digits 0, 0; blocks 3, 3) halts: step 81,375 is the halting transition F0. -/
theorem counter_3_0_3_0_halts : TM.Halts trans (counter 3 [(0, 3)] 0).toCfg :=
  halts_of_eval _ 81374 (by native_decide)

/-- `D> 0 b (ba)^7 a (ba)^4 a 1^4` (digits 0, 0; blocks 7, 4) halts: step 227,426 is the halting transition F0. -/
theorem counter_7_0_4_0_halts : TM.Halts trans (counter 7 [(0, 4)] 0).toCfg :=
  halts_of_eval _ 227425 (by native_decide)

end H44531
