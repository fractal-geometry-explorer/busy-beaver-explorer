import Rules

/-!
# 1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE: the sample K(p, q), its map, and the exact step counts

`K p q = 0^inf A> 0 1^p 0 1^q 0^inf`: two blocks of ones.  Every rule below is proved with its exact step count:

* p = 2k + 3 (odd, p ≥ 3): `K p q → K k (q + k + 4)`, i.e. `((p-3)/2, q + (p+5)/2)`, in `2k² + 10k + 13` steps
  (`K_odd`);
* p = 2k + 2 (even, p ≥ 2): `K p q → K (3k + 3 + q) 1`, i.e. `(3p/2 + q, 1)`, in `q(4k + 8) + 6k² + 22k + 15`
  steps (`K_even`): q passes of `inner_even` move the block to the right end, then `end_loop` (an inner induction
  at the blank: each round moves two ones of the block past the end and adds three ones on the left), then
  `end_fin` walks back to the left end;
* p = 0: `K 0 (q+1) → K 2 q` in 7 steps (`K_zero`);  p = 1: the machine halts (`K_one_halts`).

Blank tape reaches `K 0 2` after 7 steps (`blank_K`).  `Reduction.lean` puts these together.
-/

namespace H31371

open TM

def K (p q : Nat) : Config := ⟨blank, cons false (rep p [true] (cons false (rep q [true] blank))), .A⟩

theorem rep1_cons (k : Nat) (X : Tape) : rep k [true] (cons true X) = rep (k + 1) [true] X :=
  rep_app_comm k [true] X

theorem rep_two (k : Nat) (X : Tape) : rep (2 * k) [true] X = rep k [true, true] X := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    show cons true (cons true (rep (2 * k) [true] X)) = cons true (cons true (rep k [true, true] X))
    rw [ih]

/-- `k` passes over an odd block: `L A> 0 111 (11)^k 0 R` reaches `L 1^k A> 0 111 0 1^k R`. -/
theorem odd_iter (k : Nat) (L R : Tape) :
    steps (2 * k * k + 9 * k)
      ⟨L, cons false (cons true (cons true (cons true (rep k [true, true] (cons false R))))), .A⟩ =
      some ⟨rep k [true] L, cons false (cons true (cons true (cons true (cons false (rep k [true] R))))), .A⟩ := by
  induction k generalizing L R with
  | zero => rfl
  | succ k ih =>
    have h2 := ih (cons true L) (cons true R)
    rw [rep1_cons, rep1_cons] at h2
    exact steps_congr trans (by grind) (steps_seq trans (inner_odd k L R) h2)

theorem K_odd (k q : Nat) : steps (2 * k * k + 10 * k + 13) (K (2 * k + 3) q) = some (K k (q + k + 4)) := by
  have e : rep (2 * k + 3) [true] (cons false (rep q [true] blank)) =
      cons true (cons true (cons true (rep k [true, true] (cons false (rep q [true] blank))))) := by
    show cons true (cons true (cons true (rep (2 * k) [true] _))) = _
    rw [rep_two]
  have h1 := odd_iter k blank (rep q [true] blank)
  cases k with
  | zero => exact end_odd0 q
  | succ j =>
    have h2 := end_odd j (j + 1 + q)
    rw [← rep_add] at h1
    have e3 : (some ⟨blank, cons false (cons true (rep j [true] (cons false (cons true (cons true (cons true
        (cons true (rep (j + 1 + q) [true] blank)))))))), .A⟩ : Option Config) = some (K (j + 1) (q + (j + 1) + 4)) := by
      unfold K; rw [show q + (j + 1) + 4 = (j + 1 + q) + 4 by omega]; rfl
    have h0 : steps (2 * (j + 1) * (j + 1) + 9 * (j + 1)) (K (2 * (j + 1) + 3) q) =
        some ⟨rep (j + 1) [true] blank, cons false (cons true (cons true
        (cons true (cons false (rep (j + 1 + q) [true] blank))))), .A⟩ := by unfold K; rw [e]; exact h1
    exact steps_congr trans (by grind) (steps_seq trans h0 (h2.trans e3))

/-- `q` passes over an even block: `L A> 0 11 (11)^k 0 1^q R` reaches `L 1^q A> 0 11 (11)^k 0 R`. -/
theorem even_iter (q k : Nat) (L R : Tape) :
    steps (q * (4 * k + 7))
      ⟨L, cons false (cons true (cons true (rep k [true, true] (cons false (rep q [true] R))))), .A⟩ =
      some ⟨rep q [true] L, cons false (cons true (cons true (rep k [true, true] (cons false R)))), .A⟩ := by
  induction q generalizing L with
  | zero => exact steps_congr trans (a := 0) (by omega) rfl
  | succ q ih =>
    have h2 := ih (cons true L)
    rw [rep1_cons] at h2
    exact steps_congr trans (by grind) (steps_seq trans (inner_even k L (rep q [true] R)) h2)

/-- The even block at the blank end: `L A> 0 11 (11)^m 0^inf` reaches `L 1^(3m+1) A> 0 0 11 0^inf`. -/
theorem end_loop (m : Nat) (L : Tape) :
    steps (6 * m * m + 19 * m + 7) ⟨L, cons false (cons true (cons true (rep m [true, true] blank))), .A⟩ =
      some ⟨rep (3 * m + 1) [true] L, cons false (cons false (cons true (cons true blank))), .A⟩ := by
  induction m generalizing L with
  | zero => exact end_even0 L
  | succ j ih =>
    have h1 := end_even j L
    have h2 := inner_even j (cons true L) (cons true blank)
    have h3 := inner_even j (cons true (cons true L)) blank
    rw [cons_false_blank] at h3
    have h4 := ih (cons true (cons true (cons true L)))
    rw [rep1_cons, rep1_cons, rep1_cons] at h4
    exact steps_congr trans (by grind) (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4)))

theorem K_even (k q : Nat) :
    steps (q * (4 * k + 8) + 6 * k * k + 22 * k + 15) (K (2 * k + 2) q) = some (K (3 * k + 3 + q) 1) := by
  have e : rep (2 * k + 2) [true] (cons false (rep q [true] blank)) =
      cons true (cons true (rep k [true, true] (cons false (rep q [true] blank)))) := by
    show cons true (cons true (rep (2 * k) [true] _)) = _
    rw [rep_two]
  have h1 := even_iter q k blank blank
  rw [cons_false_blank] at h1
  have h2 := end_loop k (rep q [true] blank)
  rw [← rep_add] at h2
  have h3 := end_fin (3 * k + 1 + q)
  rw [rep1_cons] at h3
  have e3 : K (3 * k + 3 + q) 1 = ⟨blank, cons false (cons true (rep (3 * k + 1 + q + 1) [true]
      (cons false (cons true blank)))), .A⟩ := by
    unfold K; rw [show 3 * k + 3 + q = (3 * k + 1 + q + 1) + 1 by omega]; rfl
  have h0 : steps (q * (4 * k + 7)) (K (2 * k + 2) q) =
      some ⟨rep q [true] blank, cons false (cons true (cons true (rep k [true, true] blank))), .A⟩ := by
    unfold K; rw [e]; exact h1
  rw [e3]
  exact steps_congr trans (by grind) (steps_seq trans h0 (steps_seq trans h2 h3))

theorem K_zero (q : Nat) : steps 7 (K 0 (q + 1)) = some (K 2 q) := end_zero q

/-- From `K 1 q` the machine halts: six steps, then F reads 0. -/
theorem K_one_halts (q : Nat) : TM.Halts trans (K 1 q) :=
  ⟨6, ⟨blank, cons false (cons true (cons true (cons true (cons true (rep q [true] blank))))), .F⟩, rfl, rfl⟩

theorem blank_K : steps 7 init = some (K 0 2) := start

end H31371
