import Machine

/-!
# 1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF: the round laws for every block length, by induction

Write `[q, k] C> w` for `L 1^q 0 1^k C>0 w` (left tape `L` arbitrary, the head on the `0`).  The rounds of the
block machine are instances of one family of moves of the inner counter (see README.md):

* `M j k`  (k odd, q ≥ (k-1)/2):  `[q, k] C> (110)^j 0 0 R  →  [q+j, k+2j+2] C> R`;
* `Z a k`  (k odd, q ≥ (k-1)/2):  `[q, k] C> (110)^a 0 110 0 0 R  →  [q+a, k+2a+2, 3] C> R`.

Both are proved by induction on `k`: for `k ≥ 5`, one sweep (`sweep`, `k+6` steps) turns `[q+1, k]` into
`[q, 3] C> 0^(k-5) 110 …`, the odd rounds `M 0 3, M 0 5, …` (`chain`) grow the 3 back to `k-2`, and the move with one
more `110` unit (`M (j+1) (k-2)`, `Z (a+1) (k-2)`) finishes.  For `k = 3` the units `110` are absorbed one at a time
(`absorb`).  The odd round `[A, n] → [A, n+2]` is `M 0 n` and the even round `[A, n] → [A-1, n-1, 3]` is a sweep, a
chain and `Z 0 (n-3)`.  The step counts are the closed forms `3·2^((n+3)/2) − 6` and `6·2^(n/2) − 2n − 2`.
-/

namespace H168016

open TM

/-! ## Step counts -/

/-- Steps to absorb `i` units `110` in front of a block of `r` ones (state A at its left end). -/
def tA : Nat → Nat → Nat
  | 0, _ => 0
  | i + 1, r => (2 * r + 5) + tA i (r + 2)

/-- Steps of `M j (2m+3)` (closed form). -/
def TM (j m : Nat) : Nat := 24 * 2 ^ m + 2 * (j * j) + 4 * (m * j) + 11 * j - 6

/-- Steps of the chain of odd rounds `3 → 5 → … → 2t+3`. -/
def chainT : Nat → Nat
  | 0 => 0
  | t + 1 => chainT t + TM 0 t

/-- Steps of `Z a (2m+3)`. -/
def TZ : Nat → Nat → Nat
  | a, 0 => 13 + tA a 3 + (3 + 2 * a + 6)
  | a, m + 1 => (2 * m + 11) + chainT m + TZ (a + 1) m

theorem tA_eq (i r : Nat) : tA i r = 2 * (i * r) + 2 * (i * i) + 3 * i := by
  induction i generalizing r with
  | zero => simp [tA]
  | succ i ih =>
    simp only [tA, ih, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega

theorem pow_pos' (m : Nat) : 1 ≤ 2 ^ m := Nat.one_le_two_pow

theorem chainT_eq (t : Nat) : chainT t + 6 * t + 24 = 24 * 2 ^ t := by
  induction t with
  | zero => simp [chainT]
  | succ t ih =>
    have h1 := pow_pos' t
    have h2 : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [Nat.pow_succ]; omega
    simp only [chainT, TM, h2]
    omega

theorem TM_zero (j : Nat) : TM j 0 = 13 + tA j 3 + (3 + 2 * j + 2) := by
  simp only [TM, tA_eq]; omega

theorem TM_succ (j m : Nat) : TM j (m + 1) = (2 * m + 11) + chainT m + TM (j + 1) m := by
  have h1 := pow_pos' m
  have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
  have h3 := chainT_eq m
  simp only [TM, h2, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

theorem TZ_eq (a m : Nat) : TZ a m = TM a m + 4 := by
  induction m generalizing a with
  | zero => simp only [TZ, TM_zero]; omega
  | succ m ih => simp only [TZ, ih, TM_succ]; omega

/-! ## Tape helpers -/

theorem rep_double (m : Nat) (b : Bool) (s : Tape) : rep (2 * m) [b] s = rep m [b, b] s := by
  induction m generalizing s with
  | zero => rfl
  | succ m ih =>
    have e : 2 * (m + 1) = 2 * m + 2 := by omega
    rw [e, rep_add, ih]
    exact rep_app_comm m [b, b] s

/-! ## The pieces -/

/-- `[q+1, 3] C>0 W` returns to `1^(q+1) 0 A> 111 0 W` in 13 steps. -/
theorem init3 (q : Nat) (L W : Tape) :
    steps 13 ⟨rep 3 [true] (cons false (rep (q + 1) [true] L)), cons false W, .C⟩ =
      some ⟨cons false (rep (q + 1) [true] L), rep 3 [true] (cons false W), .A⟩ := rfl

/-- Absorbing one unit: `1^q 0 A> 1^r 0 110 X → 1^(q+1) 0 A> 1^(r+2) 0 X`. -/
theorem absorb (q r : Nat) (L X : Tape) :
    steps (2 * r + 5) ⟨cons false (rep q [true] L),
        rep r [true] (cons false (cons true (cons true (cons false X)))), .A⟩ =
      some ⟨cons false (rep (q + 1) [true] L), rep (r + 2) [true] (cons false X), .A⟩ := by
  have hA : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .A⟩ = some ⟨app [] (app [true] L), R, .A⟩ :=
    fun _ _ => rfl
  have h1 := cross_r trans hA r (cons false (rep q [true] L))
    (cons false (cons true (cons true (cons false X))))
  have h2 : steps 2 ⟨rep r [true] (cons false (rep q [true] L)),
      cons false (cons true (cons true (cons false X))), .A⟩ =
      some ⟨rep r [true] (cons false (rep q [true] L)), app [true] (cons true (cons true (cons false X))), .B⟩ :=
    rfl
  have hB : ∀ L R : Tape, steps 1 ⟨app [true] L, app [true] R, .B⟩ = some ⟨L, app [true] (app [true] R), .B⟩ :=
    fun _ _ => rfl
  have h3 := cross_l trans hB r (cons false (rep q [true] L)) (cons true (cons true (cons false X)))
  have h4 : steps 3 ⟨cons false (rep q [true] L), app [true] (rep r [true] (cons true (cons true (cons false X)))), .B⟩ =
      some ⟨cons false (rep (q + 1) [true] L), rep r [true] (cons true (cons true (cons false X))), .A⟩ := rfl
  have e : rep r [true] (cons true (cons true (cons false X))) = rep (r + 2) [true] (cons false X) := by
    rw [show cons true (cons true (cons false X)) = app [true] (app [true] (cons false X)) from rfl,
      rep_app_comm, rep_app_comm]
  have h := steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4))
  rw [e] at h
  have hn : r * 1 + (2 + (r * 1 + 3)) = 2 * r + 5 := by omega
  exact steps_congr trans hn h

/-- Absorbing `i` units. -/
theorem absorbs (i : Nat) : ∀ (q r : Nat) (L Y : Tape),
    steps (tA i r) ⟨cons false (rep q [true] L), rep r [true] (cons false (rep i [true, true, false] Y)), .A⟩ =
      some ⟨cons false (rep (q + i) [true] L), rep (r + 2 * i) [true] (cons false Y), .A⟩ := by
  induction i with
  | zero => intro q r L Y; rfl
  | succ i ih =>
    intro q r L Y
    have h1 := absorb q r L (rep i [true, true, false] Y)
    have h2 := ih (q + 1) (r + 2) L Y
    rw [show q + 1 + i = q + (i + 1) by omega, show r + 2 + 2 * i = r + 2 * (i + 1) by omega] at h2
    exact steps_seq trans h1 h2

/-- The end of `M`: `1^q 0 A> 1^r 0 0 0 R → 1^q 0 1^(r+2) C>0 R`. -/
theorem finM (q r : Nat) (L R : Tape) :
    steps (r + 2) ⟨cons false (rep q [true] L), rep r [true] (cons false (cons false (cons false R))), .A⟩ =
      some ⟨rep (r + 2) [true] (cons false (rep q [true] L)), cons false R, .C⟩ := by
  have hA : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .A⟩ = some ⟨app [] (app [true] L), R, .A⟩ :=
    fun _ _ => rfl
  have h1 := cross_r trans hA r (cons false (rep q [true] L)) (cons false (cons false (cons false R)))
  have h2 : steps 2 ⟨rep r [true] (cons false (rep q [true] L)), cons false (cons false (cons false R)), .A⟩ =
      some ⟨rep (r + 2) [true] (cons false (rep q [true] L)), cons false R, .C⟩ := rfl
  have hn : r * 1 + 2 = r + 2 := by omega
  exact steps_congr trans hn (steps_seq trans h1 h2)

/-- The end of `Z`: `1^q 0 A> 1^r 0 0 110 00 R → 1^q 0 1^(r+2) 0 111 C>0 R`. -/
theorem finZ (q r : Nat) (L R : Tape) :
    steps (r + 6) ⟨cons false (rep q [true] L),
        rep r [true] (cons false (cons false (cons true (cons true (cons false (cons false (cons false R))))))), .A⟩ =
      some ⟨rep 3 [true] (cons false (rep (r + 2) [true] (cons false (rep q [true] L)))), cons false R, .C⟩ := by
  have hA : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .A⟩ = some ⟨app [] (app [true] L), R, .A⟩ :=
    fun _ _ => rfl
  have h1 := cross_r trans hA r (cons false (rep q [true] L))
    (cons false (cons false (cons true (cons true (cons false (cons false (cons false R)))))))
  have h2 : steps 6 ⟨rep r [true] (cons false (rep q [true] L)),
      cons false (cons false (cons true (cons true (cons false (cons false (cons false R)))))), .A⟩ =
      some ⟨rep 3 [true] (cons false (rep (r + 2) [true] (cons false (rep q [true] L)))), cons false R, .C⟩ := rfl
  have hn : r * 1 + 6 = r + 6 := by omega
  exact steps_congr trans hn (steps_seq trans h1 h2)

/-- The sweep: `[q+1, c+5] C>0 X → [q, 3] C>0 0^c 110 X` in `c + 11` steps. -/
theorem sweep (q c : Nat) (L X : Tape) :
    steps (c + 11) ⟨rep (c + 5) [true] (cons false (rep (q + 1) [true] L)), cons false X, .C⟩ =
      some ⟨rep 3 [true] (cons false (rep q [true] L)),
        cons false (rep c [false] (cons true (cons true (cons false X)))), .C⟩ := by
  have h0 : steps 3 ⟨rep (c + 5) [true] (cons false (rep (q + 1) [true] L)), cons false X, .C⟩ =
      some ⟨rep (c + 2) [true] (cons false (rep (q + 1) [true] L)), app [true] (cons true (cons true (cons false X))), .F⟩ :=
    rfl
  have hF : ∀ L R : Tape, steps 1 ⟨app [true] L, app [true] R, .F⟩ = some ⟨L, app [true] (app [false] R), .F⟩ :=
    fun _ _ => rfl
  have h1 := cross_l trans hF (c + 2) (cons false (rep (q + 1) [true] L)) (cons true (cons true (cons false X)))
  have h2 : steps 6 ⟨cons false (rep (q + 1) [true] L),
      app [true] (rep (c + 2) [false] (cons true (cons true (cons false X)))), .F⟩ =
      some ⟨rep 3 [true] (cons false (rep q [true] L)),
        cons false (rep c [false] (cons true (cons true (cons false X)))), .C⟩ := rfl
  have hn : 3 + ((c + 2) * 1 + 6) = c + 11 := by omega
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 h2))

/-! ## The family `M` -/

/-- `M j (2m+3)`. -/
def Mstmt (m : Nat) : Prop :=
  ∀ (j q : Nat) (L R : Tape), m + 1 ≤ q →
    steps (TM j m) ⟨rep (2 * m + 3) [true] (cons false (rep q [true] L)),
        cons false (rep j [true, true, false] (cons false (cons false R))), .C⟩ =
      some ⟨rep (2 * m + 2 * j + 5) [true] (cons false (rep (q + j) [true] L)), cons false R, .C⟩

/-- The chain of odd rounds `[q, 3] C> 0^(2t) W → [q, 2t+3] C> W`. -/
theorem chain (t : Nat) (hM : ∀ i, i < t → Mstmt i) : ∀ (q : Nat) (L W : Tape), t ≤ q →
    steps (chainT t) ⟨rep 3 [true] (cons false (rep q [true] L)), cons false (rep t [false, false] W), .C⟩ =
      some ⟨rep (2 * t + 3) [true] (cons false (rep q [true] L)), cons false W, .C⟩ := by
  induction t with
  | zero => intro q L W _; rfl
  | succ t ih =>
    intro q L W hq
    have h1 := ih (fun i hi => hM i (by omega)) q L (app [false, false] W) (by omega)
    rw [rep_app_comm] at h1
    have h2 := hM t (by omega) 0 q L W (by omega)
    rw [show 2 * t + 2 * 0 + 5 = 2 * (t + 1) + 3 by omega, show q + 0 = q by omega] at h2
    exact steps_seq trans h1 h2

theorem M_zero : Mstmt 0 := by
  intro j q L R hq
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have h0 := init3 q' L (rep j [true, true, false] (cons false (cons false R)))
  have h1 := absorbs j (q' + 1) 3 L (cons false (cons false R))
  have h2 := finM (q' + 1 + j) (3 + 2 * j) L R
  rw [show 3 + 2 * j + 2 = 2 * 0 + 2 * j + 5 by omega] at h2
  rw [TM_zero, show 2 * 0 + 3 = 3 from rfl]
  exact steps_congr trans (by omega) (steps_seq trans h0 (steps_seq trans h1 h2))

theorem M_all (m : Nat) : ∀ i, i ≤ m → Mstmt i := by
  induction m with
  | zero => intro i hi; rw [show i = 0 by omega]; exact M_zero
  | succ m ih =>
    intro i hi
    by_cases h : i ≤ m
    · exact ih i h
    rw [show i = m + 1 by omega]
    intro j q L R hq
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have h0 := sweep q' (2 * m) L (rep j [true, true, false] (cons false (cons false R)))
    rw [show 2 * m + 5 = 2 * (m + 1) + 3 by omega, rep_double] at h0
    have h1 := chain m (fun i hi => ih i (by omega)) q' L
      (rep (j + 1) [true, true, false] (cons false (cons false R))) (by omega)
    have h2 := ih m (Nat.le_refl m) (j + 1) q' L R (by omega)
    rw [show 2 * m + 2 * (j + 1) + 5 = 2 * (m + 1) + 2 * j + 5 by omega,
      show q' + (j + 1) = q' + 1 + j by omega] at h2
    rw [TM_succ]
    exact steps_congr trans (by omega) (steps_seq trans h0 (steps_seq trans h1 h2))

theorem M_rule (m : Nat) : Mstmt m := M_all m m (Nat.le_refl m)

/-! ## The family `Z` -/

/-- `Z a (2m+3)`. -/
def Zstmt (m : Nat) : Prop :=
  ∀ (a q : Nat) (L R : Tape), m + 1 ≤ q →
    steps (TZ a m) ⟨rep (2 * m + 3) [true] (cons false (rep q [true] L)),
        cons false (rep a [true, true, false]
          (cons false (cons true (cons true (cons false (cons false (cons false R))))))), .C⟩ =
      some ⟨rep 3 [true] (cons false (rep (2 * m + 2 * a + 5) [true] (cons false (rep (q + a) [true] L)))),
        cons false R, .C⟩

theorem Z_rule (m : Nat) : Zstmt m := by
  induction m with
  | zero =>
    intro a q L R hq
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have h0 := init3 q' L (rep a [true, true, false]
      (cons false (cons true (cons true (cons false (cons false (cons false R)))))))
    have h1 := absorbs a (q' + 1) 3 L (cons false (cons true (cons true (cons false (cons false (cons false R))))))
    have h2 := finZ (q' + 1 + a) (3 + 2 * a) L R
    rw [show 3 + 2 * a + 2 = 2 * 0 + 2 * a + 5 by omega] at h2
    rw [show 2 * 0 + 3 = 3 from rfl]
    exact steps_congr trans (by simp only [TZ]; omega) (steps_seq trans h0 (steps_seq trans h1 h2))
  | succ m ih =>
    intro a q L R hq
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have h0 := sweep q' (2 * m) L (rep a [true, true, false]
      (cons false (cons true (cons true (cons false (cons false (cons false R)))))))
    rw [show 2 * m + 5 = 2 * (m + 1) + 3 by omega, rep_double] at h0
    have h1 := chain m (fun i _ => M_rule i) q' L
      (rep (a + 1) [true, true, false]
        (cons false (cons true (cons true (cons false (cons false (cons false R))))))) (by omega)
    have h2 := ih (a + 1) q' L R (by omega)
    rw [show 2 * m + 2 * (a + 1) + 5 = 2 * (m + 1) + 2 * a + 5 by omega,
      show q' + (a + 1) = q' + 1 + a by omega] at h2
    exact steps_congr trans (by simp only [TZ]; omega) (steps_seq trans h0 (steps_seq trans h1 h2))

/-! ## The round laws -/

theorem blank3 : (blank : Tape) = cons false (cons false (cons false blank)) := by
  rw [cons_false_blank, cons_false_blank, cons_false_blank]

theorem blank6 : (blank : Tape) =
    cons false (cons false (cons false (cons false (cons false (cons false blank))))) := by
  rw [cons_false_blank, cons_false_blank, cons_false_blank, cons_false_blank, cons_false_blank,
    cons_false_blank]

/-- **Odd round law**, every odd `n = 2m+3` and every `A ≥ (n-1)/2`:
`L 1^A 0 1^n C>0 0^∞ → L 1^A 0 1^(n+2) C>0 0^∞` in `3·2^((n+3)/2) − 6 = 24·2^m − 6` steps. -/
theorem odd_round (m A : Nat) (L : Tape) (hA : m + 1 ≤ A) :
    steps (24 * 2 ^ m - 6) ⟨rep (2 * m + 3) [true] (cons false (rep A [true] L)), blank, .C⟩ =
      some ⟨rep (2 * m + 5) [true] (cons false (rep A [true] L)), blank, .C⟩ := by
  have h := M_rule m 0 A L blank hA
  simp only [TM, Nat.mul_zero, Nat.add_zero, rep_zero] at h
  rw [← blank3, cons_false_blank] at h
  exact h

/-- **Even round law** for `n = 2m+6 ≥ 6` and every `A ≥ (n-2)/2`:
`L 1^A 0 1^n C>0 0^∞ → L 1^(A-1) 0 1^(n-1) 0 1^3 C>0 0^∞` in `6·2^(n/2) − 2n − 2 = 48·2^m − 4m − 14` steps. -/
theorem even_round (m q : Nat) (L : Tape) (hq : m + 1 ≤ q) :
    steps (48 * 2 ^ m - 4 * m - 14) ⟨rep (2 * m + 6) [true] (cons false (rep (q + 1) [true] L)), blank, .C⟩ =
      some ⟨rep 3 [true] (cons false (rep (2 * m + 5) [true] (cons false (rep q [true] L)))), blank, .C⟩ := by
  have h0 := sweep q (2 * m + 1) L (cons false (cons false blank))
  have e : ∀ Y : Tape, rep (2 * m + 1) [false] Y = rep m [false, false] (rep 1 [false] Y) := by
    intro Y; rw [rep_add, rep_double]
  rw [show 2 * m + 1 + 5 = 2 * m + 6 by omega, e] at h0
  have h1 := chain m (fun i _ => M_rule i) q L
    (rep 1 [false] (cons true (cons true (cons false (cons false (cons false blank)))))) (by omega)
  have h2 := Z_rule m 0 q L blank hq
  have h := steps_seq trans h0 (steps_seq trans h1 h2)
  rw [← blank3, cons_false_blank] at h
  have hn : 2 * m + 1 + 11 + (chainT m + TZ 0 m) = 48 * 2 ^ m - 4 * m - 14 := by
    have e1 := chainT_eq m
    have e2 := pow_pos' m
    rw [TZ_eq]; simp only [TM]; omega
  exact steps_congr trans hn h

/-- The even round for `n = 4` and every `A ≥ 1` (14 steps). -/
theorem even_round_4 (q : Nat) (L : Tape) :
    steps 14 ⟨rep 4 [true] (cons false (rep (q + 1) [true] L)), blank, .C⟩ =
      some ⟨rep 3 [true] (cons false (rep 3 [true] (cons false (rep q [true] L)))), blank, .C⟩ := by
  have h : steps 14 ⟨rep 4 [true] (cons false (rep (q + 1) [true] L)), cons false (cons false (cons false blank)), .C⟩ =
      some ⟨rep 3 [true] (cons false (rep 3 [true] (cons false (rep q [true] L)))), cons false blank, .C⟩ := rfl
  rw [← blank3, cons_false_blank] at h
  exact h

end H168016
