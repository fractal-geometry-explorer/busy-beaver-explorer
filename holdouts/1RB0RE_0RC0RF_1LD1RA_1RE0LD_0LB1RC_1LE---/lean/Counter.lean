import Collapse

/-!
# 1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---: the counter, many steps at once

The counter `gstep` of `Collapse.lean` is a binary counter whose last block `l = 4t + 1` says that the lowest `t`
bits are 0.  **Scaling** (`giter_scale`): adding `4j` to the last block makes every step of the counter take `2^j`
steps, for every state at which `gstep` is defined, whatever the zone:

    gstep x = some y   →   giter (2^j) (x.1 + 4j, x.2) = some (y.1 + 4j, y.2).

So `gfast` advances the counter by `N` steps in about two jumps per binary digit of `N`: at each jump it takes the
largest `2^s ≤ N` with `4s < l`, one step of the counter on `(l - 4s, us)`, scaled back by `4s`.  `gfast_sound`:
whatever `gfast` computes is `giter`.  With it `collapse` needs no step-by-step evaluation of the counter.
-/

namespace H4320

open TM

theorem giter_add (a b : Nat) (x : Nat × List Nat) : giter (a + b) x = (giter a x).bind (giter b) := by
  induction a generalizing x with
  | zero => simp [giter]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [giter]
    cases gstep x with
    | none => rfl
    | some y => simp only [Option.bind_some]; exact ih y

theorem gpop_succ (us : List Nat) (n : Nat) :
    gpop us (n + 1) = (gpop us n).map (fun y => (y.1 + 4, y.2)) := by
  induction us generalizing n with
  | nil => simp [gpop] <;> omega
  | cons u us ih =>
    match u with
    | 3 => simp only [gpop]; exact ih (n + 1)
    | 0 =>
      cases us with
      | nil => simp [gpop] <;> omega
      | cons w us =>
        match w with
        | 0 => rfl
        | 1 => rfl
        | w + 2 => simp [gpop] <;> omega
    | 1 => rfl
    | 2 => rfl
    | u + 4 => simp [gpop] <;> omega

/-- **Scaling.**  With `4j` more cells in the last block, one step of the counter takes `2^j` steps. -/
theorem giter_scale (j : Nat) : ∀ (x y : Nat × List Nat), gstep x = some y →
    giter (2 ^ j) (x.1 + 4 * j, x.2) = some (y.1 + 4 * j, y.2) := by
  induction j with
  | zero =>
    intro x y h
    simp only [Nat.pow_zero, Nat.mul_zero, Nat.add_zero]
    show (gstep x).bind (giter 0) = _
    rw [h]; rfl
  | succ j ih =>
    intro x y h
    obtain ⟨l, us⟩ := x
    have hl : 1 ≤ l := by
      match l, h with
      | 0, h => simp [gstep] at h
      | l + 1, _ => omega
    -- first half: the step (l + 4, us) ↦ (1, (l + 2) :: us), scaled by 4j
    have h₁ := ih (l + 4, us) (1, (l + 2) :: us) (by
      show gstep ((l + 2) + 2, us) = _; rfl)
    -- second half: one step from (1, (l + 2) :: us), scaled by 4j
    have e : gstep (1, (l + 2) :: us) = some (y.1 + 4, y.2) := by
      match l, hl, h with
      | 1, _, h =>
        simp only [gstep] at h ⊢
        show gpop (3 :: us) 0 = _
        rw [gpop, gpop_succ, h]; rfl
      | b + 2, _, h =>
        simp only [gstep, Option.some.injEq] at h
        subst h
        show gpop ((b + 4) :: us) 0 = _
        simp only [gpop]
    have h₂ := ih _ _ e
    rw [show 2 ^ (j + 1) = 2 ^ j + 2 ^ j by rw [Nat.pow_succ]; omega, giter_add]
    simp only at h₁ h₂ ⊢
    rw [show l + 4 * (j + 1) = l + 4 + 4 * j by omega, h₁, Option.bind_some,
      show y.1 + 4 * (j + 1) = y.1 + 4 + 4 * j by omega]
    exact h₂

/-- The largest `s ≤ t` with `2^s ≤ N` (or 0). -/
def pick (N : Nat) : Nat → Nat
  | 0 => 0
  | s + 1 => if 2 ^ (s + 1) ≤ N then s + 1 else pick N s

theorem pick_le (N : Nat) : ∀ t, pick N t ≤ t
  | 0 => Nat.le_refl 0
  | s + 1 => by
    simp only [pick]
    split
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le (pick_le N s)

theorem pick_pow (N : Nat) (hN : 1 ≤ N) : ∀ t, 2 ^ pick N t ≤ N
  | 0 => by simp [pick]; omega
  | s + 1 => by
    simp only [pick]
    split
    · assumption
    · exact pick_pow N hN s

/-- `N` steps of the counter, by jumps of `2^s` steps (`giter_scale`), with at most `fuel` jumps. -/
def gfast : Nat → Nat → Nat × List Nat → Option (Nat × List Nat)
  | 0, _, _ => none
  | f + 1, N, x =>
    if N = 0 then some x else
    match gstep (x.1 - 4 * pick N ((x.1 - 1) / 4), x.2) with
    | none => none
    | some y => gfast f (N - 2 ^ pick N ((x.1 - 1) / 4)) (y.1 + 4 * pick N ((x.1 - 1) / 4), y.2)

theorem gfast_sound : ∀ (f N : Nat) (x y : Nat × List Nat), gfast f N x = some y → giter N x = some y
  | 0, _, _, _, h => by simp [gfast] at h
  | f + 1, N, x, y, h => by
    simp only [gfast] at h
    split at h
    · rename_i hN; subst hN; simp only [Option.some.injEq] at h; subst h; rfl
    · rename_i hN
      cases e : gstep (x.1 - 4 * pick N ((x.1 - 1) / 4), x.2) with
      | none => rw [e] at h; simp at h
      | some z =>
        rw [e] at h
        simp only at h
        have hs := pick_le N ((x.1 - 1) / 4)
        have hp := pick_pow N (by omega) ((x.1 - 1) / 4)
        have hj := giter_scale (pick N ((x.1 - 1) / 4)) _ _ e
        simp only at hj
        have hx : x.1 - 4 * pick N ((x.1 - 1) / 4) + 4 * pick N ((x.1 - 1) / 4) = x.1 := by
          match x.1, hs, e with
          | 0, _, e => simp [gstep] at e
          | l + 1, hs, _ => omega
        rw [hx] at hj
        rw [show N = 2 ^ pick N ((x.1 - 1) / 4) + (N - 2 ^ pick N ((x.1 - 1) / 4)) by omega, giter_add]
        rw [show (x.1, x.2) = x from rfl] at hj
        rw [hj, Option.bind_some]
        exact gfast_sound f _ _ _ h

end H4320
