import CRule

/-!
# The whole sample map, and halting from blank tape as a question about its orbit

Samples `K(x, m, s)` = `0^inf 1^4 0 (10)^x 1^m C>s 0^inf` (`Kc x m s`).  The map `mstep` has six cases:

* m even, x >= 1: B, `(x-1, m+4, !s)`;
* m even, x = 0: R, `((m+6)/2, 1 or 3, 0)`;
* m odd, x = 0: H, the machine halts (`none`);
* m odd, x >= (m+5)/2: C, `(x-(m+5)/2, 2m+7-s, s)`;
* m odd, x = (m+3)/2, s = 0: A', `(2x+3, 1, 0)`;
* m odd, otherwise: A, `(2x+1, m+4-2x, !s)`.

`step_ok`: for every sample the machine does what the map says: it reaches the next sample in at least one step,
or (case H) halts.  `start`: from blank tape the machine reaches `K(7, 1, 0)` after 216 steps.  Hence
`halts_iff`: the machine halts from blank tape if and only if the orbit of `(7, 1, 0)` under the map reaches H.
Written by hand on top of `Rules.lean` (generated) and `CRule.lean`.
-/

namespace H26350

open TM

/-- The sample `K(x, m, s)`. -/
def Kc (x m : Nat) (s : Bool) : Config :=
  if m % 2 = 0 then Keven x (m / 2) s else Kodd x (m / 2) s

theorem Kc_even (x n : Nat) (s : Bool) : Kc x (2 * n) s = Keven x n s := by
  unfold Kc; rw [if_pos (by omega), show 2 * n / 2 = n by omega]

theorem Kc_odd (x n : Nat) (s : Bool) : Kc x (2 * n + 1) s = Kodd x n s := by
  unfold Kc; rw [if_neg (by omega), show (2 * n + 1) / 2 = n by omega]

/-- The map on samples; `none` is the halting case H. -/
def mstep (x m : Nat) (s : Bool) : Option (Nat × Nat × Bool) :=
  if m % 2 = 0 then
    if 1 ≤ x then some (x - 1, m + 4, !s) else some ((m + 6) / 2, if s then 3 else 1, false)
  else if x = 0 then none
  else if (m + 5) / 2 ≤ x then some (x - (m + 5) / 2, 2 * m + 7 - (if s then 1 else 0), s)
  else if x + 1 = (m + 5) / 2 ∧ s = false then some (2 * x + 3, 1, false)
  else some (2 * x + 1, m + 4 - 2 * x, !s)

/-! ## Rules A and A' for x >= 2 -/

theorem rep_double (n : Nat) (w : List Bool) (Z : Tape) : rep n (w ++ w) Z = rep (2 * n) w Z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep_succ, ← app_app, ih, show 2 * (n + 1) = 2 * n + 1 + 1 by omega, rep_succ, rep_succ]

theorem W_eq (j : Nat) (L : Tape) :
    rep (j + 1) [false, true, false, true] (cons false (cons true (cons false (cons true L)))) =
      rep (2 * j + 4) [false, true] L := by
  have h := rep_double (j + 1) [false, true] (app [false, true] (app [false, true] L))
  rw [rep_app_comm, rep_app_comm, show 2 * (j + 1) + 1 + 1 = 2 * j + 4 by omega] at h
  exact h

theorem quad_eq (j : Nat) (Z : Tape) : rep (j + 1) [true, true, true, true] Z = rep (2 * (j + 1)) [true, true] Z :=
  rep_double (j + 1) [true, true] Z

/-- Rule A, s = 0, x = j+2 <= n+1 (n = j+1+k): `K(j+2, 2n+1, 0)` reaches `K(2j+5, 2k+3, 1)`. -/
theorem ruleA0 (j k : Nat) : Adv (Kodd (j + 2) (j + 1 + k) false) (Kodd (2 * j + 5) (k + 1) true) := by
  have a : Adv (Kodd (j + 2) (j + 1 + k) false) (Q0 (j + 1) 0 (j + 1 + k)) :=
    adv_of (ph1_0 (j + 1 + k) j) (by omega) (by unfold Q0; rw [e1]; rfl)
  have b := cycN0 (j + 1) 0 0 k
  simp only [Nat.zero_add] at b
  rw [show k + (j + 1) = j + 1 + k by omega] at b
  have hf := endA0 j k
  rw [quad_eq] at hf
  have c : Reach (Q0 0 (2 * (j + 1)) k) (Kodd (2 * j + 5) (k + 1) true) := by
    refine reach_of hf ?_
    unfold Kodd
    rw [W_eq, congrArg (cons true) cons_false_blank]
    rfl
  exact a.join (b.join c)

/-- Rule A, s = 1, x = j+2 <= n+1 (n = j+1+k): `K(j+2, 2n+1, 1)` reaches `K(2j+5, 2k+3, 0)`. -/
theorem ruleA1 (j k : Nat) : Adv (Kodd (j + 2) (j + 1 + k) true) (Kodd (2 * j + 5) (k + 1) false) := by
  have a : Adv (Kodd (j + 2) (j + 1 + k) true) (Q1 (j + 1) 0 (j + 1 + k + 1)) :=
    adv_of (ph1_1 (j + 1 + k) j) (by omega) (by unfold Q1; rw [e2]; rfl)
  have b := cycN1 (j + 1) 0 0 (k + 1)
  simp only [Nat.zero_add] at b
  rw [show k + 1 + (j + 1) = j + 1 + k + 1 by omega] at b
  have hf := endA1 j k
  rw [quad_eq] at hf
  have hq : Q1 0 (2 * (j + 1)) (k + 1) = ⟨rep (2 * (j + 1)) [true, true] (cons false (rep 4 [true] blank)),
      cons true (cons true (cons true (cons false (rep k [true, false] (cons true (cons false blank)))))), .E⟩ := by
    unfold Q1
    rw [show cons true (cons false blank) = app [true, false] blank from rfl, rep_app_comm]
    rfl
  have c : Reach (Q1 0 (2 * (j + 1)) (k + 1)) (Kodd (2 * j + 5) (k + 1) false) := by
    rw [hq]
    refine reach_of hf ?_
    unfold Kodd
    rw [W_eq]
    rfl
  exact a.join (b.join c)

/-- Rule A, s = 1, x = j+2 = n+2: `K(j+2, 2j+1, 1)` reaches `K(2j+5, 1, 0)`. -/
theorem ruleA1z (j : Nat) : Adv (Kodd (j + 2) j true) (Kodd (2 * j + 5) 0 false) := by
  have a : Adv (Kodd (j + 2) j true) (Q1 (j + 1) 0 (j + 1)) :=
    adv_of (ph1_1 j j) (by omega) (by unfold Q1; rw [e2]; rfl)
  have b := cycN1 (j + 1) 0 0 0
  simp only [Nat.zero_add] at b
  have hf := endA1z j
  rw [quad_eq] at hf
  have c : Reach (Q1 0 (2 * (j + 1)) 0) (Kodd (2 * j + 5) 0 false) := by
    refine reach_of hf ?_
    unfold Kodd
    rw [W_eq]
    rfl
  exact a.join (b.join c)

theorem eight_eq (j : Nat) (L : Tape) :
    rep j [false, true] (cons false (cons true (cons false (cons true (cons false (cons true (cons false
      (cons true L)))))))) = rep (j + 4) [false, true] L := by
  have h1 := rep_app_comm j [false, true] (app [false, true] (app [false, true] (app [false, true] L)))
  have h2 := rep_app_comm (j + 1) [false, true] (app [false, true] (app [false, true] L))
  have h3 := rep_app_comm (j + 2) [false, true] (app [false, true] L)
  have h4 := rep_app_comm (j + 3) [false, true] L
  exact h1.trans (h2.trans (h3.trans h4))

/-- Rule A', x = j+2 = n+2, s = 0: `K(j+2, 2j+1, 0)` reaches `K(2j+7, 1, 0)`. -/
theorem ruleAp (j : Nat) : Adv (Kodd (j + 2) j false) (Kodd (2 * j + 7) 0 false) := by
  have a : Adv (Kodd (j + 2) j false) (Q0 (1 + j) 0 j) :=
    adv_of (ph1_0 j j) (by omega) (by unfold Q0; rw [e1, Nat.add_comm 1 j]; rfl)
  have b := cycN0 j 1 0 0
  simp only [Nat.zero_add] at b
  have hf := endAp (2 * j)
  have c : Reach (Q0 1 (2 * j) 0) (Kodd (2 * j + 7) 0 false) := by
    refine reach_of hf ?_
    unfold Kodd
    rw [eight_eq]
    rfl
  exact a.join (b.join c)

/-! ## Every case of the map -/

theorem keven_out (n : Nat) (Z : Tape) :
    rep n [false, true] (cons false (cons true (cons false (cons true Z)))) = rep (n + 2) [false, true] Z :=
  (rep_app_comm n [false, true] (app [false, true] Z)).trans (rep_app_comm (n + 1) [false, true] Z)

/-- What the machine does from a sample: the next sample in at least one step, or (case H) a halt. -/
def Ok (x m : Nat) (s : Bool) : Prop :=
  match mstep x m s with
  | none => Halts trans (Kc x m s)
  | some (x', m', s') => Adv (Kc x m s) (Kc x' m' s')

theorem ok_of {x m : Nat} {s : Bool} {x' m' : Nat} {s' : Bool} (e : mstep x m s = some (x', m', s'))
    (h : Adv (Kc x m s) (Kc x' m' s')) : Ok x m s := by
  unfold Ok; rw [e]; exact h

/-- Evaluate `mstep` on a case: split every `if`, refute the wrong branches by `omega`. -/
macro "mcalc" : tactic => `(tactic| (unfold mstep; (repeat' split) <;>
  first
  | rfl
  | (exfalso; omega)
  | (simp only [Option.some.injEq, Prod.mk.injEq, Bool.not_false, Bool.not_true, and_true, true_and,
       Bool.false_eq_true, ite_true, ite_false, reduceIte]; omega)
  | (simp_all; omega)
  | simp_all))

theorem step_ok (x m : Nat) (s : Bool) : Ok x m s := by
  obtain ⟨n, rfl | rfl⟩ : ∃ n, m = 2 * n ∨ m = 2 * n + 1 := ⟨m / 2, by omega⟩
  · -- m even
    rcases x with _ | y
    · -- R
      cases s
      · have e : mstep 0 (2 * n) false = some (n + 3, 2 * 0 + 1, false) := by
          mcalc
        refine ok_of e ?_
        rw [Kc_even, Kc_odd]
        refine adv_of (ruleR0 n) (by omega) ?_
        unfold Kodd
        rw [keven_out]
        rfl
      · have e : mstep 0 (2 * n) true = some (n + 3, 2 * 1 + 1, false) := by
          mcalc
        refine ok_of e ?_
        rw [Kc_even, Kc_odd]
        refine adv_of (ruleR1 n) (by omega) ?_
        unfold Kodd
        rw [keven_out, cons_false_blank]
        rfl
    · -- B
      have e : mstep (y + 1) (2 * n) s = some (y, 2 * (n + 2), !s) := by
        mcalc
      refine ok_of e ?_
      rw [Kc_even, Kc_even]
      cases s
      · refine adv_of (ruleB0 n y) (by omega) ?_
        unfold Keven; simp only [Bool.not_false]; rw [two_in]
      · refine adv_of (ruleB1 n y) (by omega) ?_
        unfold Keven; simp only [Bool.not_true]; rw [two_in, cons_false_blank]
  · -- m odd
    rcases x with _ | x
    · -- H
      have e : mstep 0 (2 * n + 1) s = none := by mcalc
      unfold Ok; rw [e, Kc_odd]
      cases s
      · exact ⟨_, _, toHalt0 n, halt0 n⟩
      · exact ⟨_, _, toHalt1 n, halt1 n⟩
    by_cases hC : n + 3 ≤ x + 1
    · -- C
      obtain ⟨i, hi⟩ : ∃ i, x + 1 = i + n + 3 := ⟨x + 1 - (n + 3), by omega⟩
      rw [hi]
      cases s
      · have e : mstep (i + n + 3) (2 * n + 1) false = some (i, 2 * (2 * n + 4) + 1, false) := by
          mcalc
        refine ok_of e ?_
        rw [Kc_odd, Kc_odd]; exact ruleC0 i n
      · have e : mstep (i + n + 3) (2 * n + 1) true = some (i, 2 * (2 * n + 4), true) := by
          mcalc
        refine ok_of e ?_
        rw [Kc_odd, Kc_even]; exact ruleC1 i n
    rcases x with _ | x
    · -- A with x = 1
      have hA : ¬ (0 + 1 + 1 = (2 * n + 1 + 5) / 2 ∧ s = false) := fun h => absurd h.1 (by omega)
      have e : mstep (0 + 1) (2 * n + 1) s = some (3, 2 * (n + 1) + 1, !s) := by
        mcalc
      refine ok_of e ?_
      rw [Kc_odd, Kc_odd]
      cases s
      · exact adv_of (ruleA0x1 n) (by omega) (by unfold Kodd; simp only [Bool.not_false]; rfl)
      · exact adv_of (ruleA1x1 n) (by omega) (by unfold Kodd; simp only [Bool.not_true]; rw [cons_false_blank]; rfl)
    -- x + 2 >= 2, x + 2 <= n + 2
    by_cases hP : x = n
    · subst hP
      cases s
      · -- A'
        have e : mstep (x + 1 + 1) (2 * x + 1) false = some (2 * x + 7, 2 * 0 + 1, false) := by
          mcalc
        refine ok_of e ?_
        rw [Kc_odd, Kc_odd]; exact ruleAp x
      · -- A, s = 1, x = n+2
        have hA : ¬ (x + 1 + 1 + 1 = (2 * x + 1 + 5) / 2 ∧ true = false) := fun h => Bool.noConfusion h.2
        have e : mstep (x + 1 + 1) (2 * x + 1) true = some (2 * x + 5, 2 * 0 + 1, false) := by
          mcalc
        refine ok_of e ?_
        rw [Kc_odd, Kc_odd]; exact ruleA1z x
    · -- A, x + 2 <= n + 1
      obtain ⟨k, rfl⟩ : ∃ k, n = x + 1 + k := ⟨n - (x + 1), by omega⟩
      have hA : ¬ (x + 1 + 1 + 1 = (2 * (x + 1 + k) + 1 + 5) / 2 ∧ s = false) := fun h => absurd h.1 (by omega)
      have e : mstep (x + 1 + 1) (2 * (x + 1 + k) + 1) s = some (2 * x + 5, 2 * (k + 1) + 1, !s) := by
        mcalc
      refine ok_of e ?_
      rw [Kc_odd, Kc_odd]
      cases s
      · exact ruleA0 x k
      · simp only [Bool.not_true]; exact ruleA1 x k

/-! ## From blank tape -/

/-- The orbit of the sample at step 216 under the map; `none` once it has reached H. -/
def orbit : Nat → Option (Nat × Nat × Bool)
  | 0 => some (7, 1, false)
  | t + 1 =>
    match orbit t with
    | none => none
    | some (x, m, s) => mstep x m s

/-- From blank tape the machine reaches `K(7, 1, 0)` after 216 steps. -/
theorem start : steps 216 init = some (Kc 7 1 false) := by
  have h : fsteps 216 (FCfg.blank .A) = some ⟨[true, false, true, false, true, false, true, false, true, false, true,
      false, true, false, true, false, true, true, true, true], [false], .C⟩ := by decide
  rw [show Kc 7 1 false = Kc 7 (2 * 0 + 1) false from rfl, Kc_odd]
  exact blank_reaches trans h

theorem orbit_reach (t : Nat) : ∀ x m s, orbit t = some (x, m, s) →
    ∃ N, t ≤ N ∧ steps N init = some (Kc x m s) := by
  induction t with
  | zero =>
    intro x m s h
    simp only [orbit, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨216, by omega, start⟩
  | succ t ih =>
    intro x' m' s' h
    cases ho : orbit t with
    | none => simp [orbit, ho] at h
    | some σ =>
      obtain ⟨x, m, s⟩ := σ
      have hs : mstep x m s = some (x', m', s') := by simp only [orbit, ho] at h; exact h
      obtain ⟨N, hN, hr⟩ := ih x m s ho
      have hk := step_ok x m s
      unfold Ok at hk
      rw [hs] at hk
      obtain ⟨n, hn, hc⟩ := hk
      exact ⟨N + n, by omega, steps_seq trans hr hc⟩

/-- The machine halts from blank tape if and only if the orbit of `(7, 1, 0)` under the map reaches H. -/
theorem halts_iff : HaltsFromBlank ↔ ∃ t, orbit t = none := by
  constructor
  · intro hh
    apply Classical.byContradiction
    intro hne
    have hall : ∀ t, ∃ σ, orbit t = some σ := fun t => by
      cases e : orbit t with
      | none => exact absurd ⟨t, e⟩ hne
      | some σ => exact ⟨σ, rfl⟩
    apply not_halts_of_forall trans _ hh
    apply forall_of_unbounded trans (fun N => ∃ c', steps N init = some c')
    · intro t
      obtain ⟨⟨x, m, s⟩, e⟩ := hall t
      obtain ⟨N, hN, hr⟩ := orbit_reach t x m s e
      exact ⟨N, hN, _, hr⟩
    · intro N h; exact h
  · intro ⟨t, ht⟩
    induction t with
    | zero => simp [orbit] at ht
    | succ t ih =>
      cases ho : orbit t with
      | none => exact ih ho
      | some σ =>
        obtain ⟨x, m, s⟩ := σ
        have hs : mstep x m s = none := by simp only [orbit, ho] at ht; exact ht
        obtain ⟨N, -, hr⟩ := orbit_reach t x m s ho
        have hk := step_ok x m s
        unfold Ok at hk
        rw [hs] at hk
        obtain ⟨n, c, hc, hh⟩ := hk
        exact ⟨N + n, c, steps_seq trans hr hc, hh⟩

/-- In particular: if the orbit never reaches H, the machine never halts from blank tape. -/
theorem nonhalt_of_orbit (h : ∀ t, orbit t ≠ none) : ¬ HaltsFromBlank := fun hh =>
  let ⟨t, ht⟩ := halts_iff.mp hh
  h t ht

end H26350
