import Rules

/-!
# The growth and stall phases of 1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA, by induction on the sweeps

`Rules.lean` (generated) proves that two sweeps of the bouncer eat four `110` units at the front: in the growth
phase they leave 18 ones behind the front (the tape grows by 6 cells), in the stall phase 12 (it does not grow).
Here the end configuration of each rule is put back into the shape of its start, and the rules are chained:
`4 i` units are eaten in `2 i` sweeps, for every `i`, whatever the tape `L` left of the units holds.
-/

namespace H179721

open TM

abbrev T3 : List Bool := [true, true, true]
abbrev U : List Bool := [false, true, true]

theorem cons_true_rep3 (j : Nat) (s : Tape) : cons true (rep j T3 s) = rep j T3 (cons true s) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [rep_succ, app_cons, app_nil, ih]

theorem rep3_six (j : Nat) (s : Tape) :
    rep j T3 (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true s))))))))))))))))))
      = rep (j + 6) T3 s := by
  rw [rep_add]; rfl

theorem rep3_four (j : Nat) (s : Tape) :
    rep j T3 (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true s))))))))))))
      = rep (j + 4) T3 s := by
  rw [rep_add]; rfl

/-- Growth phase configuration: `L (110)^n (111)^j 1 1 0 0 1 A> 0^inf`. -/
def gcfg (n j : Nat) (L : Tape) : Config :=
  ⟨cons true (cons false (cons false (cons true (cons true (rep j T3 (rep n U L)))))), blank, .A⟩

/-- Stall phase configuration: `L (110)^n (111)^j 1 1 0 1 1 1 D> 0^inf`. -/
def scfg (n j : Nat) (L : Tape) : Config :=
  ⟨cons true (cons true (cons true (cons false (cons true (cons true (rep j T3 (rep n U L))))))), blank, .D⟩

theorem growth_step (n j : Nat) (L : Tape) : steps (32 * j + 186) (gcfg (n + 4) j L) = some (gcfg n (j + 6) L) := by
  have h := growth_two_sweeps j n L
  rw [cons_false_blank] at h
  unfold gcfg
  rw [← rep3_six]
  simp only [cons_true_rep3] at h ⊢
  exact h

theorem stall_step (n j : Nat) (L : Tape) : steps (32 * j + 124) (scfg (n + 4) j L) = some (scfg n (j + 4) L) := by
  have h := stall_two_sweeps j n L
  rw [cons_false_blank] at h
  unfold scfg
  rw [← rep3_four]
  simp only [cons_true_rep3] at h ⊢
  exact h

/-- The growth phase: `2 i` sweeps eat `4 i` units and leave `18 i` ones. -/
theorem growth_phase (i n j : Nat) (L : Tape) : ∃ t, steps t (gcfg (n + 4 * i) j L) = some (gcfg n (j + 6 * i) L) := by
  induction i generalizing j with
  | zero => exact ⟨0, rfl⟩
  | succ i ih =>
    obtain ⟨t, ht⟩ := ih (j + 6)
    refine ⟨32 * j + 186 + t, ?_⟩
    have h1 := growth_step (n + 4 * i) j L
    rw [show n + 4 * (i + 1) = n + 4 * i + 4 by omega]
    rw [show j + 6 * (i + 1) = j + 6 + 6 * i by omega]
    exact steps_seq trans h1 ht

/-- The stall phase: `2 i` sweeps eat `4 i` units and leave `12 i` ones. -/
theorem stall_phase (i n j : Nat) (L : Tape) : ∃ t, steps t (scfg (n + 4 * i) j L) = some (scfg n (j + 4 * i) L) := by
  induction i generalizing j with
  | zero => exact ⟨0, rfl⟩
  | succ i ih =>
    obtain ⟨t, ht⟩ := ih (j + 4)
    refine ⟨32 * j + 124 + t, ?_⟩
    have h1 := stall_step (n + 4 * i) j L
    rw [show n + 4 * (i + 1) = n + 4 * i + 4 by omega]
    rw [show j + 4 * (i + 1) = j + 4 + 4 * i by omega]
    exact steps_seq trans h1 ht

end H179721
