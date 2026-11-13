import Macro

/-!
# 1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---: phases with remnants

`Macro.lean` covers a phase `S m` on an otherwise blank tape with m ≡ 0, 1 (mod 3).  When m ≡ 2 the phase leaves a
*remnant* `G k c = 0 (10)^k 1^c` to the right of the new ones, and later phases run in front of a list of remnants.
Here the phase map is extended to configurations

    P m W = 0^∞ A> 1 1 1 0 10 1^m  G k₁ c₁  G k₂ c₂ ...  0^∞        (W = [(k₁, c₁), (k₂, c₂), ...])

with the rounds `T x (m+3) → T (x+5) m` (any tape after them), and at the end of the rounds (x' = x + 5·(m/3)):

* m ≡ 0: `0^∞` → `P (2x'+10) []`;  `G (k+1) c W` → `P (2x'+11) (G k c W)`;  `G 0 c W` → `P (2x'+10+c) W`
* m ≡ 1: `0^∞` → `P (2x'+12) []`;  `G k c W`: the tape *is* `T (x'+k+1) c W` (the remnant joins the phase);
* m ≡ 2 (x' ≥ 8): `0^∞` → `P (2x'-4) [G 6 4]`;  `G k (c+3) W` → `P (2x') (G (k+7) c W)`;
  a last remnant `G k 0` → `P (2x'-4) [G 6 (2k+4)]`, `G k 1` → `P (2x'-4) [G 6 (2k+6)]`;
* not covered (`phase` returns `none`): m ≡ 2 with x' < 8, before `G k 2`, or before `G k 0`, `G k 1` that are
  not the last remnant.

`phase_correct` proves every covered case with its exact step count; `orbit_reaches` runs the map from `S 12`.
In particular the m ≡ 2 case of the clean phase is `S (3j+2) → P (10j-2) [G 6 4]` for j ≥ 2 (`phase2_clean`).
-/

set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 300000

namespace H145615

open TM

/-- A remnant `0 (10)^k 1^c`. -/
def G (k c : Nat) (R : Tape) : Tape := cons false (rep k [true, false] (rep c [true] R))

/-- A list of remnants, then blank tape. -/
def Blocks : List (Nat × Nat) → Tape
  | [] => blank
  | (k, c) :: W => G k c (Blocks W)

/-- The start of a phase in front of the remnants `W`. -/
def P (m : Nat) (W : List (Nat × Nat)) : Config := ⟨blank, T 1 m (Blocks W), .A⟩

theorem P_nil (m : Nat) : P m [] = S m := rfl

/-- Closed form of the step count of `j` rounds from `x`. -/
def rs (j x : Nat) : Nat := j * (6 * x + 51) + 15 * j * (j - 1)

theorem roundSteps_eq (j : Nat) : ∀ x, roundSteps j x = rs j x := by
  induction j with
  | zero => intro x; simp [roundSteps, rs]
  | succ j ih =>
    intro x
    simp only [roundSteps, ih, rs]
    cases j with
    | zero => simp
    | succ j => simp only [Nat.add_sub_cancel]; grind

/-- One phase from `T x m` in front of `W`: the next phase start `(m', W')` and the step count, when covered. -/
def phase (x m : Nat) : List (Nat × Nat) → Option (Nat × List (Nat × Nat) × Nat)
  | [] =>
    let x' := x + 5 * (m / 3)
    if m % 3 = 0 then some (2 * x' + 10, [], rs (m / 3) x + (4 * x' + 37) + 16)
    else if m % 3 = 1 then some (2 * x' + 12, [], rs (m / 3) x + (4 * x' + 41) + 16)
    else if 8 ≤ x' then some (2 * x' - 4, [(6, 4)], rs (m / 3) x + (4 * (x' - 8) + 115) + 16)
    else none
  | (k, c) :: W =>
    let x' := x + 5 * (m / 3)
    if m % 3 = 0 then
      (match k with
       | 0 => some (2 * x' + 10 + c, W, rs (m / 3) x + (4 * x' + 37) + 16)
       | k + 1 => some (2 * x' + 11, (k, c) :: W, rs (m / 3) x + (4 * x' + 37) + 16))
    else if m % 3 = 1 then
      (phase (x' + k + 1) c W).map fun r => (r.1, r.2.1, rs (m / 3) x + r.2.2)
    else if 8 ≤ x' then
      (if 3 ≤ c then some (2 * x', (k + 7, c - 3) :: W, rs (m / 3) x + (6 * k + 4 * (x' - 8) + 109) + 16)
       else if W = [] then
         (if c = 0 then some (2 * x' - 4, [(6, 2 * k + 4)], rs (m / 3) x + (4 * k + 4 * (x' - 8) + 115) + 16)
          else if c = 1 then some (2 * x' - 4, [(6, 2 * k + 6)], rs (m / 3) x + (4 * k + 4 * (x' - 8) + 119) + 16)
          else none)
       else none)
    else none

/-! ## Tape bookkeeping -/

theorem ones_add (a b : Nat) (R : Tape) : rep a [true] (rep b [true] R) = rep (a + b) [true] R :=
  (rep_add a b [true] R).symm

theorem ones12 (n : Nat) (R : Tape) :
    cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (rep n [true] R)))))))))))) = rep (n + 12) [true] R := rfl

theorem rep1c (n : Nat) (X : Tape) : rep n [true] (cons true X) = rep (n + 1) [true] X := rep_app_comm n [true] X

theorem rep10c (n : Nat) (X : Tape) : rep n [true, false] (cons true (cons false X)) = rep (n + 1) [true, false] X :=
  rep_app_comm n [true, false] X

/-- The restart, with the ones counted. -/
theorem restartT (n : Nat) (R : Tape) : steps 16 ⟨blank, rep (n + 2) [true] R, .C⟩ = some ⟨blank, T 1 n R, .A⟩ :=
  restart (rep n [true] R)

theorem rounds_rs (x m : Nat) (R : Tape) :
    steps (rs (m / 3) x) ⟨blank, T x m R, .A⟩ = some ⟨blank, T (x + 5 * (m / 3)) (m % 3) R, .A⟩ := by
  have h := rounds (m / 3) x (m % 3) R
  rw [roundSteps_eq, show m % 3 + 3 * (m / 3) = m by omega] at h
  exact h

/-- Glue: rounds, then a rule ending at `C>` on `1^(n+2) R`, then the restart. -/
theorem glue {x m a n : Nat} {R R' : Tape}
    (h : steps a ⟨blank, T (x + 5 * (m / 3)) (m % 3) R, .A⟩ = some ⟨blank, rep (n + 2) [true] R', .C⟩) :
    steps (rs (m / 3) x + a + 16) ⟨blank, T x m R, .A⟩ = some ⟨blank, T 1 n R', .A⟩ :=
  steps_seq trans (steps_seq trans (rounds_rs x m R) h) (restartT n R')

theorem T_join (x k c : Nat) (R : Tape) : T x 1 (G k c R) = T (x + k + 1) c R := by
  simp only [T, G]
  rw [show x + k + 1 = x + (k + 1) by omega, rep_add]
  rfl

/-! ## The covered cases -/

theorem case_zero_nil (x m : Nat) (hm : m % 3 = 0) :
    steps (rs (m / 3) x + (4 * (x + 5 * (m / 3)) + 37) + 16) ⟨blank, T x m blank, .A⟩ =
      some (P (2 * (x + 5 * (m / 3)) + 10) []) := by
  apply glue
  rw [hm]
  have h := zero (x + 5 * (m / 3))
  rw [rep_tt, show cons true blank = rep 1 [true] blank from rfl, ones_add] at h
  rw [show 2 * (x + 5 * (m / 3)) + 10 + 2 = (2 * (x + 5 * (m / 3)) + 1) + 11 by omega]
  exact h

theorem case_zero_g0 (x m c : Nat) (W : List (Nat × Nat)) (hm : m % 3 = 0) :
    steps (rs (m / 3) x + (4 * (x + 5 * (m / 3)) + 37) + 16) ⟨blank, T x m (Blocks ((0, c) :: W)), .A⟩ =
      some (P (2 * (x + 5 * (m / 3)) + 10 + c) W) := by
  apply glue
  rw [hm]
  have h := zero_r (x + 5 * (m / 3)) (rep c [true] (Blocks W))
  rw [rep_tt, ones12, ones_add] at h
  rw [show 2 * (x + 5 * (m / 3)) + 10 + c + 2 = 2 * (x + 5 * (m / 3)) + 12 + c by omega]
  exact h

theorem case_zero_g (x m k c : Nat) (W : List (Nat × Nat)) (hm : m % 3 = 0) :
    steps (rs (m / 3) x + (4 * (x + 5 * (m / 3)) + 37) + 16) ⟨blank, T x m (Blocks ((k + 1, c) :: W)), .A⟩ =
      some (P (2 * (x + 5 * (m / 3)) + 11) ((k, c) :: W)) := by
  apply glue
  rw [hm]
  have h := zero_r (x + 5 * (m / 3)) (rep (k + 1) [true, false] (rep c [true] (Blocks W)))
  have e1 : rep (k + 1) [true, false] (rep c [true] (Blocks W)) = cons true (G k c (Blocks W)) := rfl
  rw [rep_tt, ones12, e1, rep1c] at h
  rw [show 2 * (x + 5 * (m / 3)) + 11 + 2 = 2 * (x + 5 * (m / 3)) + 12 + 1 by omega]
  exact h

theorem case_one_nil (x m : Nat) (hm : m % 3 = 1) :
    steps (rs (m / 3) x + (4 * (x + 5 * (m / 3)) + 41) + 16) ⟨blank, T x m blank, .A⟩ =
      some (P (2 * (x + 5 * (m / 3)) + 12) []) := by
  apply glue
  rw [hm]
  have h := one (x + 5 * (m / 3))
  rw [rep_tt, show cons true (cons true blank) = rep 2 [true] blank from rfl, ones_add] at h
  rw [show 2 * (x + 5 * (m / 3)) + 12 + 2 = (2 * (x + 5 * (m / 3)) + 2) + 12 by omega]
  exact h

theorem case_two_nil (y m x : Nat) (hm : m % 3 = 2) (hx : x + 5 * (m / 3) = y + 8) :
    steps (rs (m / 3) x + (4 * y + 115) + 16) ⟨blank, T x m blank, .A⟩ = some (P (2 * y + 12) [(6, 4)]) := by
  apply glue
  rw [hm, hx]
  have h := two_b y
  rw [rep_tt, ones12] at h
  rw [show 2 * y + 12 + 2 = 2 * (y + 1) + 12 by omega]
  exact h

theorem case_two_c (y m x k c : Nat) (W : List (Nat × Nat)) (hm : m % 3 = 2) (hx : x + 5 * (m / 3) = y + 8) :
    steps (rs (m / 3) x + (6 * k + 4 * y + 109) + 16) ⟨blank, T x m (Blocks ((k, c + 3) :: W)), .A⟩ =
      some (P (2 * y + 16) ((k + 7, c) :: W)) := by
  apply glue
  rw [hm, hx]
  have h := two_c k y (rep c [true] (Blocks W))
  rw [rep_tt, ones12, rep10c] at h
  rw [show 2 * y + 16 + 2 = 2 * (y + 3) + 12 by omega]
  exact h

theorem case_two_0 (y m x k : Nat) (hm : m % 3 = 2) (hx : x + 5 * (m / 3) = y + 8) :
    steps (rs (m / 3) x + (4 * k + 4 * y + 115) + 16) ⟨blank, T x m (Blocks [(k, 0)]), .A⟩ =
      some (P (2 * y + 12) [(6, 2 * k + 4)]) := by
  apply glue
  rw [hm, hx]
  have h := two_0 k y
  rw [rep_tt, rep_tt, ones12, rep1c] at h
  rw [show 2 * y + 12 + 2 = 2 * (y + 1) + 12 by omega]
  exact h.trans (by rw [show 2 * k + 4 = 2 * k + 1 + 3 by omega]; rfl)

theorem case_two_1 (y m x k : Nat) (hm : m % 3 = 2) (hx : x + 5 * (m / 3) = y + 8) :
    steps (rs (m / 3) x + (4 * k + 4 * y + 119) + 16) ⟨blank, T x m (Blocks [(k, 1)]), .A⟩ =
      some (P (2 * y + 12) [(6, 2 * k + 6)]) := by
  apply glue
  rw [hm, hx]
  have h := two_1 k y
  rw [rep_tt, rep_tt, ones12, show cons true (cons true blank) = rep 2 [true] blank from rfl, ones_add] at h
  rw [show 2 * y + 12 + 2 = 2 * (y + 1) + 12 by omega]
  exact h.trans (by rw [show 2 * k + 6 = 2 * k + 2 + 4 by omega]; rfl)

/-- **Every covered case of the phase map is a run of the machine**, with its exact step count. -/
theorem phase_correct (W : List (Nat × Nat)) : ∀ x m m' W' t, phase x m W = some (m', W', t) →
    steps t ⟨blank, T x m (Blocks W), .A⟩ = some (P m' W') := by
  induction W with
  | nil =>
    intro x m m' W' t h
    simp only [phase] at h
    by_cases h0 : m % 3 = 0
    · simp only [h0, ite_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact case_zero_nil x m h0
    · by_cases h1 : m % 3 = 1
      · simp only [h0, h1, ite_true, ite_false, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact case_one_nil x m h1
      · by_cases h8 : 8 ≤ x + 5 * (m / 3)
        · simp only [h0, h1, h8, ite_true, ite_false, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          have := case_two_nil (x + 5 * (m / 3) - 8) m x (by omega) (by omega)
          rw [show 2 * (x + 5 * (m / 3) - 8) + 12 = 2 * (x + 5 * (m / 3)) - 4 by omega] at this
          exact this
        · simp [h0, h1, h8] at h
  | cons b W ih =>
    obtain ⟨k, c⟩ := b
    intro x m m' W' t h
    simp only [phase] at h
    by_cases h0 : m % 3 = 0
    · simp only [h0, ite_true] at h
      cases k with
      | zero =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact case_zero_g0 x m c W h0
      | succ k =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact case_zero_g x m k c W h0
    · by_cases h1 : m % 3 = 1
      · simp only [h0, h1, ite_true, ite_false] at h
        cases hr : phase (x + 5 * (m / 3) + k + 1) c W with
        | none => rw [hr] at h; cases h
        | some r =>
          rw [hr] at h
          simp only [Option.map, Option.some.injEq] at h
          obtain ⟨m1, W1, t1⟩ := r
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          have h2 := ih _ _ _ _ _ hr
          have h3 := rounds_rs x m (Blocks ((k, c) :: W))
          rw [h1] at h3
          have e : T (x + 5 * (m / 3)) 1 (Blocks ((k, c) :: W)) = T (x + 5 * (m / 3) + k + 1) c (Blocks W) :=
            T_join _ k c _
          rw [e] at h3
          exact steps_seq trans h3 h2
      · by_cases h8 : 8 ≤ x + 5 * (m / 3)
        · simp only [h0, h1, h8, ite_true, ite_false] at h
          obtain ⟨y, hy⟩ : ∃ y, x + 5 * (m / 3) = y + 8 := ⟨x + 5 * (m / 3) - 8, by omega⟩
          have h2 : m % 3 = 2 := by omega
          by_cases h3 : 3 ≤ c
          · simp only [h3, ite_true, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            obtain ⟨c, rfl⟩ : ∃ c', c = c' + 3 := ⟨c - 3, by omega⟩
            have := case_two_c y m x k c W h2 hy
            rw [hy, show y + 8 - 8 = y by omega, show c + 3 - 3 = c by omega,
              show 2 * (y + 8) = 2 * y + 16 by omega]
            exact this
          · simp only [h3, ite_false] at h
            by_cases hW : W = []
            · subst hW
              by_cases hc0 : c = 0
              · subst hc0
                simp only [ite_true, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                have := case_two_0 y m x k h2 hy
                rw [hy, show y + 8 - 8 = y by omega, show 2 * (y + 8) - 4 = 2 * y + 12 by omega]
                exact this
              · by_cases hc1 : c = 1
                · subst hc1
                  simp only [ite_true, ite_false, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl, rfl⟩ := h
                  have := case_two_1 y m x k h2 hy
                  rw [hy, show y + 8 - 8 = y by omega, show 2 * (y + 8) - 4 = 2 * y + 12 by omega]
                  exact this
                · simp [hc0, hc1] at h
            · simp [hW] at h
        · simp [h0, h1, h8] at h

/-- The m ≡ 2 case of a clean phase: `S (3j+2) → P (10j-2) [G 6 4]` for j ≥ 2, in exactly
`rs j 1 + 4(5j-7) + 131` steps. -/
theorem phase2_clean (j : Nat) (hj : 2 ≤ j) :
    steps (rs j 1 + (4 * (5 * j - 7) + 115) + 16) (S (3 * j + 2)) = some (P (10 * j - 2) [(6, 4)]) := by
  have := case_two_nil (5 * j - 7) (3 * j + 2) 1 (by omega) (by omega)
  rw [show (3 * j + 2) / 3 = j by omega, show 2 * (5 * j - 7) + 12 = 10 * j - 2 by omega] at this
  exact this

/-! ## The orbit from blank tape -/

/-- Iterate the phase map `n` times from `(m, W)` reached at step `t`; `none` once a case is not covered. -/
def iter : Nat → Nat × List (Nat × Nat) × Nat → Option (Nat × List (Nat × Nat) × Nat)
  | 0, s => some s
  | n + 1, (m, W, t) =>
    match phase 1 m W with
    | none => none
    | some (m', W', dt) => iter n (m', W', t + dt)

theorem iter_correct (n : Nat) : ∀ m W t m' W' t', steps t init = some (P m W) →
    iter n (m, W, t) = some (m', W', t') → steps t' init = some (P m' W') := by
  induction n with
  | zero =>
    intro m W t m' W' t' h e
    simp only [iter, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    exact h
  | succ n ih =>
    intro m W t m' W' t' h e
    simp only [iter] at e
    cases hp : phase 1 m W with
    | none => rw [hp] at e; cases e
    | some r =>
      obtain ⟨m1, W1, dt⟩ := r
      rw [hp] at e
      exact ih m1 W1 (t + dt) m' W' t' (steps_seq trans h (phase_correct W 1 m m1 W1 dt hp)) e

/-- From `S 12` (step 75): if `iter n` is defined, the machine is at that phase start at that step. -/
theorem orbit_reaches (n : Nat) {m W t} (e : iter n (12, [], 75) = some (m, W, t)) : steps t init = some (P m W) :=
  iter_correct n 12 [] 75 m W t init_S12 e

/-- A halt after `N` steps comes after every phase start the covered map reaches. -/
theorem lt_of_halts {N : Nat} {c : Config} (hN : steps N init = some c) (hc : step c = none)
    {t m : Nat} {W : List (Nat × Nat)} (h : steps t init = some (P m W)) : t < N := by
  refine Nat.lt_of_not_le fun hle => ?_
  obtain ⟨d, rfl⟩ : ∃ d, t = N + d := ⟨t - N, by omega⟩
  cases d with
  | zero =>
    rw [Nat.add_zero, hN] at h
    cases h
    exact absurd hc (by simp [step, TM.step, P, T, trans, cons])
  | succ d =>
    have h' : steps (N + (d + 1)) init = none := steps_halt trans hN hc d
    rw [h'] at h
    cases h

/-- The covered map takes the run through `n` phases, the last one reached after at least `2^b` steps. -/
def deep (n b : Nat) : Bool :=
  match iter n (12, [], 75) with
  | some (_, _, t) => decide (2 ^ b ≤ t)
  | none => false

theorem halt_after {n b : Nat} (hd : deep n b = true) {N : Nat} {c : Config} (hN : steps N init = some c)
    (hc : step c = none) : 2 ^ b < N := by
  unfold deep at hd
  split at hd
  · rename_i m W t e
    have := lt_of_halts hN hc (orbit_reaches n e)
    have : 2 ^ b ≤ t := of_decide_eq_true hd
    omega
  · cases hd

/-- **If the machine halts from blank tape, it runs more than 2^6953 steps first**: 2,000 phases of the proved
map, evaluated by Lean's kernel. -/
theorem halt_time_kernel {N : Nat} {c : Config} (hN : steps N init = some c) (hc : step c = none) :
    2 ^ 6953 < N :=
  halt_after (n := 2000) (by decide +kernel) hN hc

/-- The same through 61,963 phases (compiled evaluation): more than 2^215260 steps. -/
theorem halt_time_native {N : Nat} {c : Config} (hN : steps N init = some c) (hc : step c = none) :
    2 ^ 215260 < N :=
  halt_after (n := 61963) (by native_decide) hN hc

end H145615
