import Events

/-!
# 1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB: the event orbit, evaluated

A machine that started on blank tape `n` steps ago has no 1 further than `n` cells from where its head is
(`far_cell`).  So when the event orbit reaches an anchor `Y 1^m C> 0 1^c Z`, the machine has already run at least
`c` steps without halting (`long_run`).  Evaluating the event orbit then gives a number of steps before which the
machine does not halt: 10^137 by Lean's kernel alone, 10^13275 by compiled evaluation.
-/

set_option exponentiation.threshold 20000

namespace H134427

open TM

/-- Both sides of the tape are blank from some distance on: the left from `a`, the right (head cell included)
from `b`. -/
def Within (a b : Nat) (c : Config) : Prop := (∀ k, a ≤ k → c.l k = false) ∧ (∀ k, b ≤ k → c.r k = false)

theorem within_step {a b : Nat} {c c' : Config} (hb : 1 ≤ b) (h : Within a b c) (hs : step c = some c') :
    ∃ a' b', 1 ≤ b' ∧ a' + b' ≤ a + b + 1 ∧ Within a' b' c' := by
  obtain ⟨l, r, q⟩ := c
  obtain ⟨hl, hr⟩ := h
  simp only [step, TM.step] at hs
  cases ht : trans q (r 0) with
  | none => rw [ht] at hs; cases hs
  | some t =>
    obtain ⟨w, d, q'⟩ := t
    rw [ht] at hs
    cases d with
    | R =>
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨a + 1, b, hb, by omega, ?_, ?_⟩
      · intro k hk
        cases k with
        | zero => omega
        | succ k => exact hl k (by omega)
      · intro k hk; exact hr (k + 1) (by omega)
    | L =>
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨a, b + 1, by omega, by omega, ?_, ?_⟩
      · intro k hk; exact hl (k + 1) (by omega)
      · intro k hk
        cases k with
        | zero => omega
        | succ k =>
          cases k with
          | zero => omega
          | succ k => exact hr (k + 1) (by omega)

theorem within_steps : ∀ (n : Nat) {a b : Nat} {c c' : Config}, 1 ≤ b → Within a b c → steps n c = some c' →
    ∃ a' b', a' + b' ≤ a + b + n ∧ Within a' b' c'
  | 0, a, b, c, c', _, h, hs => by
    simp only [steps_zero, Option.some.injEq] at hs; subst hs; exact ⟨a, b, by omega, h⟩
  | n + 1, a, b, c, c', hb, h, hs => by
    cases h1 : step c with
    | none => rw [show steps (n + 1) c = none from by simp [steps, TM.steps, h1]] at hs; cases hs
    | some c1 =>
      have hs : steps n c1 = some c' := (steps_succ_of_step trans n h1).symm.trans hs
      obtain ⟨a1, b1, hb1, hab, hw⟩ := within_step hb h h1
      obtain ⟨a2, b2, hab2, hw2⟩ := within_steps n hb1 hw hs
      exact ⟨a2, b2, by omega, hw2⟩

/-- After `n` steps from blank tape there is no 1 at distance more than `n` to the right of the head. -/
theorem far_cell {n j : Nat} {c : Config} (hs : steps n init = some c) (hj : c.r j = true) : j ≤ n := by
  obtain ⟨a, b, hab, _, hr⟩ := within_steps n (a := 0) (b := 1) (Nat.le_refl 1) ⟨fun _ _ => rfl, fun _ _ => rfl⟩ hs
  refine Classical.byContradiction fun hlt => ?_
  have := hr j (by omega)
  rw [hj] at this; cases this

theorem ones_get : ∀ (c k : Nat) (X : Tape), k < c → rep c [true] X k = true
  | 0, _, _, h => by omega
  | _ + 1, 0, _, _ => rfl
  | c + 1, k + 1, X, h => ones_get c k X (by omega)

/-- The event orbit of the first anchor reaches, after `K` events, an anchor whose block right of the head has at
least `B` ones (and at least one). -/
def bigAt (K B : Nat) : Bool :=
  match evOrbit first K with
  | some ⟨_, .C, (1, c) :: _⟩ => decide (1 ≤ c ∧ B ≤ c)
  | _ => false

/-- If the event orbit reaches an anchor with at least `B` ones right of the head, the machine does not halt in its
first `B` steps from blank tape. -/
theorem long_run (K B : Nat) (h : bigAt K B = true) : ∀ n ≤ B, ∃ c, steps n init = some c := by
  unfold bigAt at h
  split at h
  · rename_i l c Z he
    have hc : 1 ≤ c ∧ B ≤ c := of_decide_eq_true h
    obtain ⟨t, ht⟩ := blank_first.trans (evOrbit_reaches K first _ he)
    have hcell : (cfg ⟨l, .C, (1, c) :: Z⟩).r c = true := by
      obtain ⟨j, rfl⟩ : ∃ j, c = j + 1 := ⟨c - 1, by omega⟩
      exact ones_get (j + 1) j _ (by omega)
    have hle := far_cell ht hcell
    intro n hn
    exact steps_le trans (a := n) (b := t - n) (by rw [show n + (t - n) = t by omega]; exact ht)
  · cases h

set_option maxRecDepth 100000 in
/-- The machine does not halt in its first 10^137 steps (Lean's kernel: 29,996 events). -/
theorem no_halt_kernel : ∀ n ≤ 10 ^ 137, ∃ c, steps n init = some c :=
  long_run 29996 (10 ^ 137) (by decide +kernel)

/-- The machine does not halt in its first 10^13275 steps (compiled evaluation: 2,999,995 events). -/
theorem no_halt_native : ∀ n ≤ 10 ^ 13275, ∃ c, steps n init = some c :=
  long_run 2999995 (10 ^ 13275) (by native_decide)

end H134427
