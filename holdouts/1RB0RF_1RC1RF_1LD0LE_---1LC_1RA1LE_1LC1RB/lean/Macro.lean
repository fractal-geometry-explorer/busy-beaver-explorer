import Pass

/-!
# 1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB: the run is the orbit of a map on block lengths

The rules of `Rules.lean`, put together.  With
  `P n = 0^inf 1^n B> 0^inf`,  `Q n = 0^inf 1^n F> 0^inf`,  `X a b c = 0^inf 1^a E> 0 1^b 0 1^c 0^inf`,
a pass from `P (n+1)` goes to `X 0 n 2` (`pstart`), and from `X 0 b c` the machine either halts or reaches
`P (g b c)`, where (`xrun`)
* `g 0 c = c + 2` for even c, and `(3c + 9)/2` for odd c (through `Q`);
* `g (2i+2) c = c + 3i + 5` (the even zigzag: `X a (2i+2) c -> X (a+c) (2i+2) 0 -> ... -> X (a+3i+1) 0 2`);
* `g 1 c` halts;
* `g (2i+3) c = g i (c + i + 4)` (the odd zigzag `X 0 (2i+3) c -> X (i+1) 1 (c+i+1)`, then `X (i+1) 1 c' -> X 0 i (c'+3)`).
From blank tape the machine reaches `P 4`, so it halts exactly when the orbit of 4 under `n ↦ g (n-1) 2` reaches
`none` (`halts_iff`).  `f n = g (n-1) 2` is `none` exactly when `n + 2` is a power of two, at least 4 (`f_none_iff`).
-/

namespace H144815

open TM

/-- `0^inf 1^a E> 0 1^b 0 1^c 0^inf`. -/
def X (a b c : Nat) : Config := ⟨rep a [true] blank, cons false (rep b [true] (cons false (rep c [true] blank))), .E⟩
/-- `0^inf 1^n F> 0^inf`. -/
def Q (n : Nat) : Config := ⟨rep n [true] blank, blank, .F⟩

theorem n_tt (n : Nat) (s : Tape) : rep n [true, true] s = rep (2 * n) [true] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    simp [ih]

theorem n_cons (n : Nat) (s : Tape) : cons true (rep n [true] s) = rep (n + 1) [true] s := rfl
theorem n_rep (a b : Nat) (s : Tape) : rep a [true] (rep b [true] s) = rep (a + b) [true] s := (rep_add a b _ s).symm
theorem n_blank : cons true blank = rep 1 [true] blank := rfl
theorem n_false (s : Tape) : cons true (cons false s) = rep 1 [true] (cons false s) := rfl

theorem rep_congr {a b : Nat} {s s' : Tape} (w : List Bool) (h : a = b) (hs : s = s') : rep a w s = rep b w s' := by
  rw [h, hs]
theorem cons_congr {s s' : Tape} (x : Bool) (h : s = s') : cons x s = cons x s' := by rw [h]
theorem cfg_congr {l l' r r' : Tape} (q : St) (h₁ : l = l') (h₂ : r = r') :
    (⟨l, r, q⟩ : Config) = ⟨l', r', q⟩ := by rw [h₁, h₂]

/-- Normalise both sides to blocks `rep N [true]` and match the counts with `omega`. -/
macro "tnorm" : tactic => `(tactic| (
  simp only [X, P, Q, n_tt, n_blank, n_false, n_cons, n_rep, rep_zero, cons_false_blank];
  repeat (first | rfl | (apply cfg_congr) | (apply rep_congr; omega) | (apply cons_congr))))

theorem parity (n : Nat) : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩

/-- `c` reaches `c'` in a positive number of steps. -/
def Reaches1 (c c' : Config) : Prop := ∃ n, 0 < n ∧ steps n c = some c'

theorem of_rule {c c' d d' : Config} {n : Nat} (hn : 0 < n) (h : steps n c = some c') (e : d = c) (e' : d' = c') :
    Reaches1 d d' := ⟨n, hn, by rw [e, e']; exact h⟩

theorem Reaches1.trans {a b c : Config} (h₁ : Reaches1 a b) (h₂ : Reaches1 b c) : Reaches1 a c := by
  obtain ⟨n, hn, h⟩ := h₁
  obtain ⟨m, _, h'⟩ := h₂
  exact ⟨n + m, by omega, steps_seq H144815.trans h h'⟩

theorem Reaches1.halts {a b : Config} (h₁ : Reaches1 a b) (h₂ : TM.Halts H144815.trans b) :
    TM.Halts H144815.trans a := by
  obtain ⟨n, _, h⟩ := h₁
  obtain ⟨m, c, h', hc⟩ := h₂
  exact ⟨n + m, c, steps_seq H144815.trans h h', hc⟩

/-- `P (n+1) -> X 0 n 2`. -/
theorem pstart (n : Nat) : Reaches1 (P (n + 1)) (X 0 n 2) := by
  rcases parity n with ⟨k, rfl | rfl⟩
  · cases k with
    | zero => exact of_rule (by omega) p_start_1 (by tnorm) (by tnorm)
    | succ k => exact of_rule (by omega) (p_start_o k) (by tnorm) (by tnorm)
  · exact of_rule (by omega) (p_start_e k) (by tnorm) (by tnorm)

/-- `Q (n+2) -> X 0 (n+1) 1`. -/
theorem qstart (n : Nat) : Reaches1 (Q (n + 2)) (X 0 (n + 1) 1) := by
  rcases parity n with ⟨k, rfl | rfl⟩
  · exact of_rule (by omega) (q_start_e k) (by tnorm) (by tnorm)
  · exact of_rule (by omega) (q_start_o k) (by tnorm) (by tnorm)

/-- The odd zigzag: `X a (2i+3) c -> X (a+i+1) 1 (c+i+1)`. -/
theorem odd_run (i : Nat) : ∀ a c, Reaches1 (X a (2 * i + 3) c) (X (a + i + 1) 1 (c + i + 1)) := by
  induction i with
  | zero => intro a c; exact of_rule (by omega) (odd_round0 a c) (by tnorm) (by tnorm)
  | succ i ih =>
    intro a c
    have h1 : Reaches1 (X a (2 * (i + 1) + 3) c) (X (a + 1) (2 * i + 3) (c + 1)) :=
      of_rule (by omega) (odd_round a c i) (by tnorm) (by tnorm)
    have h2 := ih (a + 1) (c + 1)
    rw [show a + 1 + i + 1 = a + (i + 1) + 1 by omega, show c + 1 + i + 1 = c + (i + 1) + 1 by omega] at h2
    exact h1.trans h2

/-- `X (a+1) 1 c -> X 0 a (c+3)`. -/
theorem odd_end (a c : Nat) : Reaches1 (X (a + 1) 1 c) (X 0 a (c + 3)) := by
  rcases parity a with ⟨k, rfl | rfl⟩
  · cases k with
    | zero => exact of_rule (by omega) (odd_end_1 c) (by tnorm) (by tnorm)
    | succ k => exact of_rule (by omega) (odd_end_o k c) (by tnorm) (by tnorm)
  · exact of_rule (by omega) (odd_end_e k c) (by tnorm) (by tnorm)

/-- `X 0 1 c` halts. -/
theorem xhalt (c : Nat) : TM.Halts H144815.trans (X 0 1 c) := by
  refine ⟨6, ⟨blank, cons false (cons true (cons true (cons true (cons true (rep c [true] blank))))), .D⟩, ?_, rfl⟩
  have e : X 0 1 c = ⟨blank, cons false (cons true (cons false (rep c [true] blank))), .E⟩ := by tnorm
  rw [e]; exact halt c

/-- The even zigzag: `X a (2i+2) c -> X (a+c) (2i+2) 0` (in zero or more steps, stated for c+1). -/
theorem even_run (i : Nat) (c : Nat) : ∀ a, Reaches1 (X a (2 * i + 2) (c + 1)) (X (a + c + 1) (2 * i + 2) 0) := by
  induction c with
  | zero => intro a; exact of_rule (by omega) (even_round a 0 i) (by tnorm) (by tnorm)
  | succ c ih =>
    intro a
    have h1 : Reaches1 (X a (2 * i + 2) (c + 1 + 1)) (X (a + 1) (2 * i + 2) (c + 1)) :=
      of_rule (by omega) (even_round a (c + 1) i) (by tnorm) (by tnorm)
    have h2 := ih (a + 1)
    rw [show a + 1 + c + 1 = a + (c + 1) + 1 by omega] at h2
    exact h1.trans h2

/-- `X a (2i+2) 0 -> X (a+3i+1) 0 2`. -/
theorem even_down (i : Nat) : ∀ a, Reaches1 (X a (2 * i + 2) 0) (X (a + 3 * i + 1) 0 2) := by
  induction i with
  | zero => intro a; exact of_rule (by omega) (even_zero0 a) (by tnorm) (by tnorm)
  | succ i ih =>
    intro a
    have h1 : Reaches1 (X a (2 * (i + 1) + 2) 0) (X (a + 1) (2 * i + 2) 2) :=
      of_rule (by omega) (even_zero a i) (by tnorm) (by tnorm)
    have h2 := even_run i 1 (a + 1)
    have h3 := ih (a + 1 + 1 + 1)
    rw [show a + 1 + 1 + 1 + 3 * i + 1 = a + 3 * (i + 1) + 1 by omega] at h3
    exact (h1.trans h2).trans h3

theorem zero_end_e (a j : Nat) : Reaches1 (X a 0 (2 * j)) (P (a + 2 * j + 2)) :=
  of_rule (by omega) (zero_even a j) (by tnorm) (by tnorm)

theorem zero_end_o (a j : Nat) : Reaches1 (X a 0 (2 * j + 1)) (Q (a + 2 * j + 3)) :=
  of_rule (by omega) (zero_odd a j) (by tnorm) (by tnorm)

/-- From `X 0 (2i+2) c` the machine reaches `P (c+3i+5)`. -/
theorem even_full (i c : Nat) : Reaches1 (X 0 (2 * i + 2) c) (P (c + 3 * i + 5)) := by
  have hd : ∀ a, Reaches1 (X a (2 * i + 2) 0) (P (a + 3 * i + 5)) := by
    intro a
    have h := (even_down i a).trans (zero_end_e (a + 3 * i + 1) 1)
    rw [show a + 3 * i + 1 + 2 * 1 + 2 = a + 3 * i + 5 by omega] at h
    exact h
  cases c with
  | zero => simpa using hd 0
  | succ c =>
    have h := (even_run i c 0).trans (hd (0 + c + 1))
    rw [show 0 + c + 1 + 3 * i + 5 = c + 1 + 3 * i + 5 by omega] at h
    exact h

/-- The block length after the pass from `X 0 b c`, or `none` if the machine halts. -/
def g (b c : Nat) : Option Nat :=
  if b = 0 then some (if c % 2 = 0 then c + 2 else (3 * c + 9) / 2)
  else if b % 2 = 0 then some (c + 3 * (b / 2) + 2)
  else if h : b = 1 then none
  else g ((b - 3) / 2) (c + (b - 3) / 2 + 4)
termination_by b
decreasing_by omega

/-- **From `X 0 b c` the machine reaches `P m` if `g b c = some m`, and halts if `g b c = none`.** -/
theorem xrun_lt (N : Nat) : ∀ b, b < N → ∀ c, (∀ m, g b c = some m → Reaches1 (X 0 b c) (P m)) ∧
    (g b c = none → TM.Halts H144815.trans (X 0 b c)) := by
  induction N with
  | zero => intro b hb; omega
  | succ N ihN =>
    intro b hbN c
    have ih : ∀ b', b' < b → ∀ c, (∀ m, g b' c = some m → Reaches1 (X 0 b' c) (P m)) ∧
        (g b' c = none → TM.Halts H144815.trans (X 0 b' c)) := fun b' hb' => ihN b' (by omega)
    rcases parity b with ⟨k, rfl | rfl⟩
    · cases k with
      | zero =>
        rw [g]; simp only [ite_true]
        refine ⟨fun m hm => ?_, fun hm => by simp at hm⟩
        simp only [Option.some.injEq] at hm
        subst hm
        rcases parity c with ⟨j, rfl | rfl⟩
        · have h := zero_end_e 0 j
          rw [show 0 + 2 * j + 2 = 2 * j + 2 by omega] at h
          simpa [show 2 * j % 2 = 0 by omega] using h
        · have h1 := zero_end_o 0 j
          have hq := qstart (2 * j + 1)
          have h2 := even_full j 1
          rw [show 0 + 2 * j + 3 = 2 * j + 1 + 2 by omega] at h1
          rw [show 2 * j + 1 + 1 = 2 * j + 2 by omega] at hq
          have h := (h1.trans hq).trans h2
          rw [show (2 * j + 1) % 2 = 1 by omega, show (3 * (2 * j + 1) + 9) / 2 = 1 + 3 * j + 5 by omega]
          simpa using h
      | succ k =>
        have hb : 2 * (k + 1) = 2 * k + 2 := by omega
        rw [g]
        simp only [show 2 * (k + 1) ≠ 0 by omega, show 2 * (k + 1) % 2 = 0 by omega, ite_true, ite_false]
        refine ⟨fun m hm => ?_, fun hm => by simp at hm⟩
        simp only [Option.some.injEq] at hm
        subst hm
        rw [hb]
        have h := even_full k c
        rw [show c + 3 * k + 5 = c + 3 * ((2 * k + 2) / 2) + 2 by omega] at h
        exact h
    · cases k with
      | zero =>
        rw [g]; simp only [show 2 * 0 + 1 ≠ 0 by omega, ite_false, dite_true]
        exact ⟨fun m hm => by simp at hm, fun _ => xhalt c⟩
      | succ i =>
        have hb : 2 * (i + 1) + 1 = 2 * i + 3 := by omega
        rw [g]
        simp only [show 2 * (i + 1) + 1 ≠ 0 by omega, show (2 * (i + 1) + 1) % 2 ≠ 0 by omega,
          show 2 * (i + 1) + 1 ≠ 1 by omega, ite_false, dite_false]
        rw [show (2 * (i + 1) + 1 - 3) / 2 = i by omega]
        have hz := odd_run i 0 c
        have he := odd_end i (c + i + 1)
        rw [show 0 + i + 1 = i + 1 by omega] at hz
        rw [show c + i + 1 + 3 = c + i + 4 by omega] at he
        have hr := ih i (by omega) (c + i + 4)
        rw [hb]
        exact ⟨fun m hm => (hz.trans he).trans (hr.1 m hm), fun hm => (hz.trans he).halts (hr.2 hm)⟩

theorem xrun (b c : Nat) : (∀ m, g b c = some m → Reaches1 (X 0 b c) (P m)) ∧
    (g b c = none → TM.Halts H144815.trans (X 0 b c)) := xrun_lt (b + 1) b (by omega) c

/-- The pass map on block lengths: `P n` leads to `P (f n)`, or halts for `none`. -/
def f (n : Nat) : Option Nat := g (n - 1) 2

/-- One pass: `P (n+1)` reaches `P m` when `f (n+1) = some m`, and halts when it is `none`. -/
theorem pass (n : Nat) : (∀ m, f (n + 1) = some m → Reaches1 (P (n + 1)) (P m)) ∧
    (f (n + 1) = none → TM.Halts H144815.trans (P (n + 1))) := by
  have h := xrun n 2
  simp only [f, show n + 1 - 1 = n by omega]
  exact ⟨fun m hm => (pstart n).trans (h.1 m hm), fun hm => (pstart n).halts (h.2 hm)⟩

theorem g_pos_lt (N : Nat) : ∀ b, b < N → ∀ c m, g b c = some m → 0 < m := by
  induction N with
  | zero => intro b hb; omega
  | succ N ihN =>
    intro b hbN c m h
    have ih : ∀ b', b' < b → ∀ c m, g b' c = some m → 0 < m := fun b' hb' => ihN b' (by omega)
    rw [g] at h
    by_cases h0 : b = 0
    · simp only [h0, ite_true, Option.some.injEq] at h; split at h <;> omega
    by_cases h2 : b % 2 = 0
    · simp only [h0, h2, ite_true, ite_false, Option.some.injEq] at h; omega
    by_cases h1 : b = 1
    · simp [h1] at h
    simp only [h0, h2, h1, ite_false, dite_false] at h
    exact ih _ (by omega) _ _ h

theorem g_pos (b c m : Nat) (h : g b c = some m) : 0 < m := g_pos_lt (b + 1) b (by omega) c m h

theorem pow4 (j : Nat) : 2 ^ (j + 2) = 4 * 2 ^ j := by
  rw [Nat.pow_succ, Nat.pow_succ]; omega

theorem g_none_lt (N : Nat) : ∀ b, b < N → ∀ c, (g b c = none ↔ ∃ j, b + 3 = 2 ^ (j + 2)) := by
  induction N with
  | zero => intro b hb; omega
  | succ N ihN =>
    intro b hbN c
    rw [g]
    by_cases h0 : b = 0
    · subst h0
      simp only [ite_true, reduceCtorEq, false_iff]
      intro ⟨j, hj⟩; rw [pow4] at hj; have := Nat.one_le_two_pow (n := j); omega
    by_cases h2 : b % 2 = 0
    · simp only [h0, h2, ite_true, ite_false, reduceCtorEq, false_iff]
      intro ⟨j, hj⟩; rw [pow4] at hj; omega
    by_cases h1 : b = 1
    · subst h1; simp only [show (1 : Nat) ≠ 0 by omega, ite_false, dite_true, true_iff]
      exact ⟨0, rfl⟩
    simp only [h0, h2, h1, ite_false, dite_false]
    rw [ihN _ (by omega)]
    constructor
    · intro ⟨j, hj⟩; exact ⟨j + 1, by rw [pow4] at hj ⊢; rw [Nat.pow_succ]; omega⟩
    · intro ⟨j, hj⟩
      cases j with
      | zero => simp at hj; omega
      | succ j => exact ⟨j, by rw [pow4] at hj ⊢; rw [Nat.pow_succ] at hj; omega⟩

/-- **A pass halts exactly when n + 2 is a power of two (at least 4).** -/
theorem f_none_iff (n : Nat) : f (n + 1) = none ↔ ∃ j, n + 3 = 2 ^ (j + 2) := by
  simp only [f, show n + 1 - 1 = n by omega]
  exact g_none_lt (n + 1) n (by omega) 2

/-- The orbit of 4 under `f`. -/
def orbit : Nat → Option Nat
  | 0 => some 4
  | i + 1 => match orbit i with
    | none => none
    | some n => f n

theorem orbit_pos (i : Nat) : ∀ n, orbit i = some n → 0 < n := by
  cases i with
  | zero => intro n h; simp [orbit] at h; omega
  | succ i =>
    intro n h
    simp only [orbit] at h
    split at h
    · cases h
    · exact g_pos _ _ _ h

theorem orbit_run (i : Nat) : ∀ n, orbit i = some n → ∃ s, i ≤ s ∧ steps s init = some (P n) := by
  induction i with
  | zero =>
    intro n h
    simp [orbit] at h
    subst h
    exact ⟨9, by omega, blank_P4⟩
  | succ i ih =>
    intro n h
    simp only [orbit] at h
    cases ho : orbit i with
    | none => rw [ho] at h; cases h
    | some p =>
      rw [ho] at h
      obtain ⟨s, hs, hr⟩ := ih p ho
      have hp := orbit_pos i p ho
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      obtain ⟨m, hm, hr'⟩ := (pass q).1 n h
      exact ⟨s + m, by omega, steps_seq H144815.trans hr hr'⟩

/-- **The machine halts from blank tape exactly when the orbit of 4 under `f` reaches `none`.** -/
theorem halts_iff : HaltsFromBlank ↔ ∃ i, orbit i = none := by
  constructor
  · intro hh
    apply Classical.byContradiction
    intro hno
    have hall : ∀ i, ∃ p, orbit i = some p := by
      intro i
      cases h : orbit i with
      | none => exact absurd ⟨i, h⟩ hno
      | some p => exact ⟨p, rfl⟩
    apply not_halts_of_forall H144815.trans _ hh
    apply forall_of_unbounded H144815.trans (fun n => ∃ c, steps n init = some c)
    · intro n
      obtain ⟨p, h⟩ := hall n
      obtain ⟨m, hm, hr⟩ := orbit_run n p h
      exact ⟨m, hm, _, hr⟩
    · intro m hm; exact hm
  · intro ⟨i, hi⟩
    induction i with
    | zero => simp [orbit] at hi
    | succ i ih =>
      simp only [orbit] at hi
      cases ho : orbit i with
      | none => exact ih ho
      | some p =>
        rw [ho] at hi
        obtain ⟨s, -, hr⟩ := orbit_run i p ho
        have hp := orbit_pos i p ho
        obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
        obtain ⟨m, c, h₁, h₂⟩ := (pass q).2 hi
        exact ⟨s + m, c, steps_seq H144815.trans hr h₁, h₂⟩

theorem orbit_none_succ (i : Nat) (h : orbit i = none) : orbit (i + 1) = none := by
  simp [orbit, h]

theorem orbit_some_of_le {i k : Nat} (hik : i ≤ k) (h : (orbit k).isSome = true) : (orbit i).isSome = true := by
  induction hik with
  | refl => exact h
  | step _ ih =>
    apply ih
    cases ho : orbit _ with
    | none => rw [orbit_none_succ _ ho] at h; cases h
    | some _ => rfl

/-- The orbit of 4 avoids `none` for 10,000 passes (evaluated by compiled code: `native_decide`). -/
theorem orbit_10000 : (orbit 10000).isSome = true := by native_decide

/-- So the run from blank tape does not halt within its first 10,000 passes. -/
theorem no_halt_10000 (i : Nat) (hi : i ≤ 10000) : orbit i ≠ none := by
  have h := orbit_some_of_le hi orbit_10000
  intro hn; rw [hn] at h; cases h

end H144815
