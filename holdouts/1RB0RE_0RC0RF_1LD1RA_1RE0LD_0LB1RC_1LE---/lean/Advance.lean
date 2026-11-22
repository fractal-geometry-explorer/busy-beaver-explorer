import Counter
import General

/-!
# 1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---: part of a collapse, in closed form

`advance` (`Collapse.lean`) gives `N` sub-rounds of `W` with the counter, for `N` up to the collapse time, with the
digits after them as `Witer N (q, D)`.  `W` takes 1 off the time left `T` (`T_W`) and keeps the mass (`mass_W`),
and `T` is one to one (`T_inj`: the list is the binary expansion), so the digits after `N` sub-rounds are the only
list `D'` with `T D' + N = T D`, and the first block is fixed by the mass.  `advance_to`: no step of `W` is
evaluated, only `T`, so `N` can be as large as `T D` (about `2^100` here).
-/

namespace H4320

open TM

theorem pow_odd_inj : ∀ (x y a b : Nat), 2 ^ x * (1 + 2 * a) = 2 ^ y * (1 + 2 * b) → x = y ∧ a = b
  | 0, 0, a, b, h => by simp at h; omega
  | 0, y + 1, a, b, h => by
    rw [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_comm (2 ^ y) 2, Nat.mul_assoc] at h; omega
  | x + 1, 0, a, b, h => by
    rw [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_comm (2 ^ x) 2, Nat.mul_assoc] at h; omega
  | x + 1, y + 1, a, b, h => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_comm (2 ^ x) 2, Nat.mul_comm (2 ^ y) 2, Nat.mul_assoc,
      Nat.mul_assoc] at h
    have := pow_odd_inj x y a b (by omega)
    omega

/-- `T` is one to one. -/
theorem T_inj : ∀ (D D' : List Nat), T D = T D' → D = D'
  | [], [], _ => rfl
  | [], x :: r, h => by have := T_pos x r; rw [← h] at this; simp [T] at this
  | x :: r, [], h => by have := T_pos x r; rw [h] at this; simp [T] at this
  | x :: r, y :: s, h => by
    simp only [T] at h
    obtain ⟨hx, ht⟩ := pow_odd_inj x y _ _ h
    rw [hx, T_inj r s ht]

theorem Witer_T (N : Nat) : ∀ (q : Nat) (D : List Nat), N ≤ T D → T (Witer N (q, D)).2 + N = T D := by
  induction N with
  | zero => intro q D _; rfl
  | succ N ih =>
    intro q D h
    cases D with
    | nil => simp [T] at h
    | cons a ds =>
      have e := T_W q a ds
      show T (Witer N (W q (a :: ds))).2 + (N + 1) = _
      generalize W q (a :: ds) = p at e ⊢
      obtain ⟨q', D'⟩ := p
      have := ih q' D' (by simp only at e; omega)
      simp only at e this ⊢
      omega

theorem Witer_mass (N : Nat) : ∀ (q : Nat) (D : List Nat),
    mass (Witer N (q, D)).1 (Witer N (q, D)).2 = mass q D := by
  induction N with
  | zero => intro q D; rfl
  | succ N ih =>
    intro q D
    cases D with
    | nil => exact ih q []
    | cons a ds =>
      show mass (Witer N (W q (a :: ds))).1 (Witer N (W q (a :: ds))).2 = _
      have e := mass_W q a ds
      generalize W q (a :: ds) = p at e ⊢
      obtain ⟨q', D'⟩ := p
      rw [ih]; exact e

/-- **Part of a collapse.**  `N` sub-rounds from `enc q D`, the counter advanced `N` times, to the digits `D'` with
`T D' + N = T D` and the same mass. -/
theorem advance_to (N q q' : Nat) (D D' : List Nat) (x y : Nat × List Nat) (hT : T D' + N = T D)
    (hm : mass q' D' = mass q D) (hy : giter N x = some y) :
    ∃ n, steps n (enc q D x.1 x.2) = some (enc q' D' y.1 y.2) := by
  obtain ⟨n, h⟩ := advance N q D x y (by omega) hy
  have h₁ := Witer_T N q D (by omega)
  have h₂ : (Witer N (q, D)).2 = D' := T_inj _ _ (by omega)
  have h₃ := Witer_mass N q D
  rw [h₂] at h₃
  have h₄ : (Witer N (q, D)).1 = q' := by simp only [mass] at h₃ hm; omega
  rw [h₂, h₄] at h
  exact ⟨n, h⟩

/-- A pass of the pass machine between two configurations of the counter form. -/
theorem pass_to (fuel N q q' : Nat) (D D' : List Nat) (l l' : Nat) (us us' : List Nat) (n : Nat)
    (h : subs fuel N (encBlocks q D) l us = .moment (encBlocks q' D') l' us' n) :
    steps n (enc q D l us) = some (enc q' D' l' us') := by
  rw [enc_gcfg q D, enc_gcfg q' D']
  exact subs_moment fuel N _ _ _ _ _ _ _ h

end H4320
