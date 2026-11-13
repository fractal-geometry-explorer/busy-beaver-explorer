import Phase2

set_option linter.unusedSimpArgs false

/-!
# 1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE: the first phase of a round, and the map

* `V K i m` = `0^inf 1^(2K) 0 A> 0 (10)^(2i) 111 0 (10)^m 1 0^inf`
* `W3 x`    = `0^inf C> 0 (10)^x 111 0^inf`,  `W2 x` = `0^inf C> 0 (10)^x 11 0^inf`

`S (n+1)` reaches `V n 0 0`.  From `V K i m` each bounce (`b1`) moves two ones of the left block to a pair `10`
of the middle block; when the right block `(10)^m` is used up, `b2` moves the `2i` pairs to the right block, and
when the left block runs out the phase ends in one of six ways.  `ph K i m` is the next sample, `none` for a halt.
`halts_iff_orbit`: the machine halts from blank tape iff the orbit of 1 under `next n = ph (n - 1) 0 0` hits none.
-/

namespace H87254

open TM

def V (K i m : Nat) : Config :=
  ⟨cons false (rep (2 * K) [true] blank), cons false (rep (2 * i) [true, false] (cons true (cons true (cons true
    (cons false (rep m [true, false] (cons true blank))))))), .A⟩

def W3 (x : Nat) : Config := ⟨blank, cons false (rep x [true, false] (cons true (cons true (cons true blank)))), .C⟩
def W2 (x : Nat) : Config := ⟨blank, cons false (rep x [true, false] (cons true (cons true blank))), .C⟩

/-- The outcome of the first phase from `V K i m` (and the second phase after it): the next sample, or `none`. -/
def ph : Nat → Nat → Nat → Option Nat
  | 0, i, 0 => some (4 * i + 7)
  | 1, i, 0 => some (4 * i + 10)
  | 2, _, 0 => none
  | 3, i, 0 => some (2 * i + 9)
  | K + 4, i, 0 => ph K 0 (2 * i + 5)
  | 0, i, m + 1 => some (4 * i + m + 8)
  | K + 1, i, m + 1 => ph K (i + 1) m

theorem rep_one_two (K : Nat) (s : Tape) : rep (2 * (K + 1)) [true] s = cons true (cons true (rep (2 * K) [true] s)) := by
  rw [show 2 * (K + 1) = 2 * K + 1 + 1 by omega]; rfl

theorem rep_comm_tf (n : Nat) (s : Tape) :
    rep n [true, false] (cons true (cons false s)) = cons true (cons false (rep n [true, false] s)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show cons true (cons false (rep n [true, false] (cons true (cons false s)))) = _
    rw [ih]; rfl

theorem v1 (K i m : Nat) : steps (8 * i + 12) (V (K + 1) i (m + 1)) = some (V K (i + 1) m) := by
  have h := b1 i (2 * K) m blank (cons true blank)
  simp only [← rot_tf, rep_succ, app_cons, app_nil] at h
  simp only [V, rep_one_two, show 2 * (i + 1) = 2 * i + 1 + 1 by omega, rep_succ, app_cons, app_nil]
  exact h

theorem v2 (K i : Nat) : steps (24 * i + 62) (V (K + 4) i 0) = some (V K 0 (2 * i + 5)) := by
  have h := b2 i (2 * K)
  simp only [V, show 2 * (K + 4) = 2 * K + 8 by omega, show 2 * i + 5 = 2 * i + 1 + 1 + 1 + 1 + 1 by omega, ← rot_tf, rep_succ, rep_zero, app_cons, app_nil, rep_comm_tf, Nat.mul_zero] at h ⊢
  exact h

theorem v3 (i m : Nat) : steps (8 * i + 10) (V 0 i (m + 1)) = some (T (2 * i + 2) m) := by
  have h := b3 i m
  simp only [V, T, show 2 * i + 2 = 2 * i + 1 + 1 by omega, ← rot_tf, rep_succ, rep_zero, app_cons, app_nil, rep_comm_tf, Nat.mul_zero] at h ⊢
  exact h

theorem v_e0 (i : Nat) : steps (8 * i + 10) (V 0 i 0) = some (W3 (2 * i + 2)) := by
  have h := e0 i
  simp only [V, W3, show 2 * i + 2 = 2 * i + 1 + 1 by omega, ← rot_tf, rep_succ, rep_zero, app_cons, app_nil, rep_comm_tf, Nat.mul_zero] at h ⊢
  exact h

theorem v_e1 (i : Nat) : steps (16 * i + 30) (V 1 i 0) = some (W2 (2 * i + 4)) := by
  have h := e1 i
  simp only [V, W2, show 2 * i + 4 = 2 * i + 1 + 1 + 1 + 1 by omega, ← rot_tf, rep_succ, rep_zero, app_cons, app_nil, rep_comm_tf, Nat.mul_zero] at h ⊢
  exact h

theorem v_e2 (i : Nat) : ∃ c, steps (24 * i + 56) (V 2 i 0) = some c ∧ step c = none :=
  ⟨_, e2 i, rfl⟩

theorem v_e3 (i : Nat) : steps (24 * i + 60) (V 3 i 0) = some (T 0 (2 * i + 5)) := by
  have h := e3 i
  simp only [V, T, show 2 * i + 5 = 2 * i + 1 + 1 + 1 + 1 + 1 by omega, ← rot_tf, rep_succ, rep_zero, app_cons, app_nil, rep_comm_tf, Nat.mul_zero] at h ⊢
  exact h

theorem x3 (x : Nat) : steps (2 * x + 16) (W3 (x + 1)) = some (U (2 * x + 1) 2) := by
  have h := w3 x
  simp only [rep_tt] at h
  exact h

theorem x2 (x : Nat) : steps (2 * x + 12) (W2 (x + 1)) = some (U (2 * x + 1) 1) := by
  have h := w2 x
  simp only [rep_tt] at h
  exact h

theorem s_v (n : Nat) : ∃ t, 0 < t ∧ steps t (S (n + 1)) = some (V n 0 0) := by
  match n with
  | 0 => exact ⟨17, by omega, p1⟩
  | 1 => exact ⟨19, by omega, p2⟩
  | n + 2 =>
    refine ⟨2 * n + 21, by omega, ?_⟩
    have h := p0 n
    simp only [rep_tt] at h
    simp only [S, V, show 2 * (n + 2) = 2 * (n + 2) from rfl, show 2 * 0 = 0 from rfl, rep_zero]
    exact h

/-- A run from `U (2j+1) m` through the second phase. -/
theorem u_s (j m : Nat) : ∃ t, steps t (U (2 * j + 1) m) = some (S (m + 2 * j + 3)) := by
  obtain ⟨t, h⟩ := u2_iter j m
  exact ⟨t + (4 * (m + 2 * j) + 10), steps_seq trans h (u3 (m + 2 * j))⟩

/-- **The first phase**, for all `K i m`: `V K i m` reaches the sample `S n` if `ph K i m = some n`, and halts if
`ph K i m = none`. -/
theorem ph_spec (K : Nat) : ∀ i m, (∀ n, ph K i m = some n → ∃ t, steps t (V K i m) = some (S n)) ∧
    (ph K i m = none → Halts trans (V K i m)) := by
  induction K using Nat.strongRecOn with
  | _ K ih =>
  intro i m
  cases m with
  | zero =>
    match K with
    | 0 =>
      refine ⟨fun n hn => ?_, fun hn => by simp [ph] at hn⟩
      simp only [ph, Option.some.injEq] at hn; subst hn
      obtain ⟨t, h⟩ := u_s (2 * i + 1) 2
      rw [show 2 + 2 * (2 * i + 1) + 3 = 4 * i + 7 by omega] at h
      have h0 := x3 (2 * i + 1)
      rw [show 2 * i + 1 + 1 = 2 * i + 2 by omega, show 2 * (2 * i + 1) + 1 = 2 * (2 * i + 1) + 1 from rfl] at h0
      exact ⟨_, steps_seq trans (v_e0 i) (steps_seq trans h0 h)⟩
    | 1 =>
      refine ⟨fun n hn => ?_, fun hn => by simp [ph] at hn⟩
      simp only [ph, Option.some.injEq] at hn; subst hn
      obtain ⟨t, h⟩ := u_s (2 * i + 3) 1
      rw [show 1 + 2 * (2 * i + 3) + 3 = 4 * i + 10 by omega] at h
      have h0 := x2 (2 * i + 3)
      rw [show 2 * i + 3 + 1 = 2 * i + 4 by omega] at h0
      exact ⟨_, steps_seq trans (v_e1 i) (steps_seq trans h0 h)⟩
    | 2 =>
      refine ⟨fun n hn => by simp [ph] at hn, fun _ => ?_⟩
      obtain ⟨c, hc, hs⟩ := v_e2 i
      exact ⟨_, c, hc, hs⟩
    | 3 =>
      refine ⟨fun n hn => ?_, fun hn => by simp [ph] at hn⟩
      simp only [ph, Option.some.injEq] at hn; subst hn
      obtain ⟨t, h⟩ := phase2 0 (2 * i + 5)
      rw [show 2 * 0 + (2 * i + 5) + 4 = 2 * i + 9 by omega] at h
      exact ⟨_, steps_seq trans (v_e3 i) h⟩
    | K + 4 =>
      obtain ⟨h1, h2⟩ := ih K (by omega) 0 (2 * i + 5)
      refine ⟨fun n hn => ?_, fun hn => ?_⟩
      · obtain ⟨t, h⟩ := h1 n (by simpa [ph] using hn)
        exact ⟨_, steps_seq trans (v2 K i) h⟩
      · obtain ⟨t, c, hc, hs⟩ := h2 (by simpa [ph] using hn)
        exact ⟨_, c, steps_seq trans (v2 K i) hc, hs⟩
  | succ m =>
    match K with
    | 0 =>
      refine ⟨fun n hn => ?_, fun hn => by simp [ph] at hn⟩
      simp only [ph, Option.some.injEq] at hn; subst hn
      obtain ⟨t, h⟩ := phase2 (2 * i + 2) m
      rw [show 2 * (2 * i + 2) + m + 4 = 4 * i + m + 8 by omega] at h
      exact ⟨_, steps_seq trans (v3 i m) h⟩
    | K + 1 =>
      obtain ⟨h1, h2⟩ := ih K (by omega) (i + 1) m
      refine ⟨fun n hn => ?_, fun hn => ?_⟩
      · obtain ⟨t, h⟩ := h1 n (by simpa [ph] using hn)
        exact ⟨_, steps_seq trans (v1 K i m) h⟩
      · obtain ⟨t, c, hc, hs⟩ := h2 (by simpa [ph] using hn)
        exact ⟨_, c, steps_seq trans (v1 K i m) hc, hs⟩

theorem ph_pos (K : Nat) : ∀ i m n, ph K i m = some n → 1 ≤ n := by
  induction K using Nat.strongRecOn with
  | _ K ih =>
  intro i m n hn
  cases m with
  | zero =>
    match K with
    | 0 => simp only [ph, Option.some.injEq] at hn; omega
    | 1 => simp only [ph, Option.some.injEq] at hn; omega
    | 2 => simp [ph] at hn
    | 3 => simp only [ph, Option.some.injEq] at hn; omega
    | K + 4 => exact ih K (by omega) 0 (2 * i + 5) n (by simpa [ph] using hn)
  | succ m =>
    match K with
    | 0 => simp only [ph, Option.some.injEq] at hn; omega
    | K + 1 => exact ih K (by omega) (i + 1) m n (by simpa [ph] using hn)

/-- The map on the samples: `S n` (n ≥ 1) to `S (next n)`, `none` for a halt. -/
def next (n : Nat) : Option Nat := ph (n - 1) 0 0

def orbit : Nat → Option Nat
  | 0 => some 1
  | k + 1 => (orbit k).bind next

theorem blank_4 : steps 4 init = some (S 1) := rfl

theorem orbit_reach (k : Nat) : ∀ n, orbit k = some n → 1 ≤ n ∧ ∃ t, k ≤ t ∧ steps t init = some (S n) := by
  induction k with
  | zero =>
    intro n hn; simp only [orbit, Option.some.injEq] at hn; subst hn
    exact ⟨by omega, 4, by omega, blank_4⟩
  | succ k ih =>
    intro n' hn'
    simp only [orbit] at hn'
    cases e : orbit k with
    | none => rw [e] at hn'; cases hn'
    | some n =>
      rw [e] at hn'
      simp only [Option.bind_some, next] at hn'
      obtain ⟨hn1, t, hkt, ht⟩ := ih n e
      obtain ⟨n0, rfl⟩ : ∃ n0, n = n0 + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hn'
      obtain ⟨t1, ht1, h1⟩ := s_v n0
      obtain ⟨t2, h2⟩ := (ph_spec n0 0 0).1 n' hn'
      exact ⟨ph_pos n0 0 0 n' hn', t + (t1 + t2), by omega,
        steps_seq trans ht (steps_seq trans h1 h2)⟩

/-- **The reduction**: the machine halts from blank tape iff the orbit of 1 under `next` reaches `none`. -/
theorem halts_iff_orbit : HaltsFromBlank ↔ ∃ k, orbit k = none := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    have hall : ∀ k, ∃ n, orbit k = some n := by
      intro k
      cases e : orbit k with
      | none => exact absurd ⟨k, e⟩ hno
      | some n => exact ⟨n, rfl⟩
    apply not_halts_of_forall trans _ hH
    apply forall_of_unbounded trans (fun t => ∃ n, steps t init = some (S n))
    · intro k
      obtain ⟨n, hn⟩ := hall k
      obtain ⟨_, t, hkt, h⟩ := orbit_reach k n hn
      exact ⟨t, hkt, n, h⟩
    · rintro t ⟨n, h⟩; exact ⟨_, h⟩
  · rintro ⟨k, hk⟩
    induction k with
    | zero => cases hk
    | succ k ih =>
      simp only [orbit] at hk
      cases e : orbit k with
      | none => exact ih e
      | some n =>
        rw [e] at hk
        simp only [Option.bind_some, next] at hk
        obtain ⟨hn1, t, _, ht⟩ := orbit_reach k n e
        obtain ⟨n0, rfl⟩ : ∃ n0, n = n0 + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel] at hk
        obtain ⟨t1, _, h1⟩ := s_v n0
        obtain ⟨t2, c, hc, hs⟩ := (ph_spec n0 0 0).2 hk
        exact ⟨t + (t1 + t2), c, steps_seq trans ht (steps_seq trans h1 hc), hs⟩

end H87254
