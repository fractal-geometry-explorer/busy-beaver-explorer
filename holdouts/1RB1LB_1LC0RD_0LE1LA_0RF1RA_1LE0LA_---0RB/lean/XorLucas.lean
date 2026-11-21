import Xor

/-!
# Many epochs: rule 102 and Lucas' theorem

`Xor.lean` shows that one epoch maps a word string `w` to `x102 w q` (cell `i` becomes `w[i] xor w[i+1]`, with the fixed
value `q` after the end).  Here that map is iterated.  Extending `w` by `q` and then `x`s forever (`ext`), every iterate is
the plain rule 102 on the infinite row (`ext_xit`), and by Lucas' theorem mod 2

  cell `i` after `t` epochs = XOR over the `k ≤ t` whose binary digits lie inside those of `t` of cell `i + k` at the start

(`closed_form`; `disj k (t - k)` is "`k` and `t - k` share no binary 1", i.e. `C(t, k)` is odd).  For a gap of `n` `x`s
before a `y` (`allx`): word `i` after `t` epochs is `y` iff `j = n - i ≤ t` and `C(t, j)` is odd, so the whole gap is `y`
exactly when the binary digits of `t` contain those of every `j ≤ n`, first at `t = 2^b - 1` with `2^b > n`.

The Lucas lemmas (`disj`, `pascal_rule`, `xsum`) are copied from the Pascal-triangle machine
1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF (`Lucas.lean` there).
-/

namespace H696

open TM

/-! ## Lucas' theorem mod 2 (as in `Lucas.lean` of 1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF) -/

/-- `a` and `b` have no binary 1 in the same place (Lucas: `C(a + b, a)` is odd). -/
def disj (a b : Nat) : Bool :=
  if a = 0 then true
  else if b = 0 then true
  else (!(a % 2 == 1 && b % 2 == 1)) && disj (a / 2) (b / 2)
termination_by a
decreasing_by omega

theorem disj_zero_left (b : Nat) : disj 0 b = true := by
  rw [disj]; simp

theorem disj_zero_right (a : Nat) : disj a 0 = true := by
  rw [disj]; simp

/-- One binary digit at a time, for all `a b`. -/
theorem disj_eq (a b : Nat) : disj a b = ((!(a % 2 == 1 && b % 2 == 1)) && disj (a / 2) (b / 2)) := by
  by_cases ha : a = 0
  · subst ha; simp [disj_zero_left]
  · by_cases hb : b = 0
    · subst hb; simp [disj_zero_right]
    · rw [disj]; simp [ha, hb]

/-- **Pascal's rule for `disj`**: `C(a+b, a) = C(a+b-1, a) + C(a+b-1, a-1)`, mod 2, on the bit test. -/
theorem pascal_rule : ∀ a b : Nat, 0 < a → 0 < b → disj a b = bne (disj a (b - 1)) (disj (a - 1) b) := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
    intro b ha hb
    rw [disj_eq a b, disj_eq a (b - 1), disj_eq (a - 1) b]
    have ma : a % 2 = 0 ∨ a % 2 = 1 := by omega
    have mb : b % 2 = 0 ∨ b % 2 = 1 := by omega
    rcases ma with ma | ma <;> rcases mb with mb | mb
    · -- both even: one digit down, and Pascal's rule there
      have e1 : (b - 1) % 2 = 1 := by omega
      have e2 : (a - 1) % 2 = 1 := by omega
      have e3 : (b - 1) / 2 = b / 2 - 1 := by omega
      have e4 : (a - 1) / 2 = a / 2 - 1 := by omega
      rw [ma, mb, e1, e2, e3, e4]
      have z : ((0 : Nat) == 1) = false := rfl
      have o : ((1 : Nat) == 1) = true := rfl
      rw [z, o]
      simp only [Bool.false_and, Bool.not_false, Bool.true_and, Bool.and_false]
      exact ih (a / 2) (by omega) (b / 2) (by omega) (by omega)
    · -- a even, b odd
      have e1 : (b - 1) % 2 = 0 := by omega
      have e2 : (a - 1) % 2 = 1 := by omega
      have e3 : (b - 1) / 2 = b / 2 := by omega
      have e4 : (a - 1) / 2 = a / 2 - 1 := by omega
      rw [ma, mb, e1, e2, e3, e4]
      simp
    · -- a odd, b even
      have e1 : (b - 1) % 2 = 1 := by omega
      have e2 : (a - 1) % 2 = 0 := by omega
      have e3 : (b - 1) / 2 = b / 2 - 1 := by omega
      have e4 : (a - 1) / 2 = a / 2 := by omega
      rw [ma, mb, e1, e2, e3, e4]
      simp
    · -- both odd: C(a+b, a) is even, and the two terms cancel
      have e1 : (b - 1) % 2 = 0 := by omega
      have e2 : (a - 1) % 2 = 0 := by omega
      have e3 : (b - 1) / 2 = b / 2 := by omega
      have e4 : (a - 1) / 2 = a / 2 := by omega
      rw [ma, mb, e1, e2, e3, e4]
      simp

/-- XOR of `f 0, ..., f (n-1)`. -/
def xsum : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, f => bne (xsum n f) (f n)

theorem xsum_congr (n : Nat) (f g : Nat → Bool) (h : ∀ k, k < n → f k = g k) : xsum n f = xsum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xsum]
    rw [ih (fun k hk => h k (by omega)), h n (by omega)]

theorem xsum_bne (n : Nat) (f g : Nat → Bool) :
    xsum n (fun k => bne (f k) (g k)) = bne (xsum n f) (xsum n g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xsum]
    rw [ih]
    cases xsum n f <;> cases xsum n g <;> cases f n <;> cases g n <;> rfl


theorem xsum_shift (n : Nat) (f : Nat → Bool) : xsum (n + 1) f = bne (f 0) (xsum n (fun k => f (k + 1))) := by
  induction n with
  | zero => simp [xsum]
  | succ n ih =>
    show bne (xsum (n + 1) f) (f (n + 1)) = bne (f 0) (bne (xsum n (fun k => f (k + 1))) (f (n + 1)))
    rw [ih]
    cases f 0 <;> cases xsum n (fun k => f (k + 1)) <;> cases f (n + 1) <;> rfl

/-! ## Rule 102 on an infinite row -/

/-- One step of rule 102: cell `i` becomes `d i xor d (i + 1)`. -/
def S (d : Nat → Bool) : Nat → Bool := fun i => bne (d i) (d (i + 1))

/-- `t` steps of rule 102. -/
def Si : Nat → (Nat → Bool) → (Nat → Bool)
  | 0, d => d
  | t + 1, d => S (Si t d)

theorem Si_S (t : Nat) (d : Nat → Bool) : Si t (S d) = S (Si t d) := by
  induction t with
  | zero => rfl
  | succ t ih => show S (Si t (S d)) = S (S (Si t d)); rw [ih]

/-- The closed form: XOR of `d (i + k)` over the `k ≤ t` with `C(t, k)` odd. -/
def cf (d : Nat → Bool) (t i : Nat) : Bool := xsum (t + 1) (fun k => d (i + k) && disj k (t - k))

theorem cf_succ (d : Nat → Bool) (t i : Nat) : cf d (t + 1) i = bne (cf d t i) (cf d t (i + 1)) := by
  unfold cf
  -- split C(t+1, k) = C(t, k) + C(t, k-1) termwise
  have split : xsum (t + 2) (fun k => d (i + k) && disj k (t + 1 - k)) =
      xsum (t + 2) (fun k => bne (d (i + k) && (decide (k ≤ t) && disj k (t - k)))
        (d (i + k) && (decide (0 < k) && disj (k - 1) (t + 1 - k)))) := by
    apply xsum_congr
    intro k hk
    by_cases k0 : k = 0
    · subst k0
      simp [disj_zero_left]
    · by_cases kt : k = t + 1
      · subst kt
        have z : decide (t + 1 ≤ t) = false := by simp
        rw [z]
        cases d (i + (t + 1)) <;> simp [disj_zero_right]
      · have a1 : decide (k ≤ t) = true := by simp; omega
        have a2 : decide (0 < k) = true := by simp; omega
        rw [a1, a2, pascal_rule k (t + 1 - k) (by omega) (by omega)]
        have e : t + 1 - k - 1 = t - k := by omega
        rw [e]
        cases d (i + k) <;> simp
  rw [split, xsum_bne]
  -- the first sum: its last term is 0
  have s1 : xsum (t + 2) (fun k => d (i + k) && (decide (k ≤ t) && disj k (t - k))) =
      xsum (t + 1) (fun k => d (i + k) && disj k (t - k)) := by
    show bne (xsum (t + 1) _) (d (i + (t + 1)) && (decide (t + 1 ≤ t) && disj (t + 1) (t - (t + 1)))) = _
    have z : decide (t + 1 ≤ t) = false := by simp
    rw [z]
    simp only [Bool.false_and, Bool.and_false, Bool.bne_false]
    apply xsum_congr
    intro k hk
    have a1 : decide (k ≤ t) = true := by simp; omega
    rw [a1, Bool.true_and]
  -- the second sum: shift by one
  have s2 : xsum (t + 2) (fun k => d (i + k) && (decide (0 < k) && disj (k - 1) (t + 1 - k))) =
      xsum (t + 1) (fun k => d (i + 1 + k) && disj k (t - k)) := by
    rw [xsum_shift]
    have z : decide (0 < 0) = false := by simp
    rw [z]
    simp only [Bool.false_and, Bool.and_false, Bool.false_bne]
    apply xsum_congr
    intro k hk
    have a1 : decide (0 < k + 1) = true := by simp
    have e1 : k + 1 - 1 = k := by omega
    have e2 : t + 1 - (k + 1) = t - k := by omega
    have e3 : i + (k + 1) = i + 1 + k := by omega
    rw [a1, e1, e2, e3, Bool.true_and]
  rw [s1, s2]

/-- **Lucas' theorem for rule 102**: `t` steps from `d`, cell `i`, is the XOR of `d (i + k)` over the `k ≤ t` whose binary
digits are disjoint from those of `t - k` (i.e. `C(t, k)` odd). -/
theorem Si_cf (d : Nat → Bool) (t : Nat) : ∀ i, Si t d i = cf d t i := by
  induction t with
  | zero => intro i; simp [Si, cf, xsum, disj_zero_left]
  | succ t ih =>
    intro i
    show bne (Si t d i) (Si t d (i + 1)) = _
    rw [ih i, ih (i + 1), cf_succ]

/-! ## Back to word strings -/

/-- A word string followed by `q`, then `x`s forever. -/
def ext : List Bool → Bool → Nat → Bool
  | [], q, 0 => q
  | [], _, _ + 1 => false
  | a :: _, _, 0 => a
  | _ :: ws, q, j + 1 => ext ws q j

theorem ext_lt (ws : List Bool) (q : Bool) : ∀ i, i < ws.length → ext ws q i = ws.getD i false := by
  induction ws with
  | nil => intro i h; simp at h
  | cons a ws ih =>
    intro i h
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simp at h; omega)

/-- One epoch with `q` after the end is one step of rule 102 on the extended row. -/
theorem ext_x102 (ws : List Bool) (q : Bool) : ext (x102 ws q) q = S (ext ws q) := by
  funext i
  induction ws generalizing i with
  | nil => cases i <;> cases q <;> rfl
  | cons a ws ih =>
    cases i with
    | zero => cases ws <;> rfl
    | succ i => exact ih i

/-- `t` epochs (each with `q` after the end). -/
def xit : Nat → List Bool → Bool → List Bool
  | 0, ws, _ => ws
  | t + 1, ws, q => xit t (x102 ws q) q

theorem ext_xit (t : Nat) : ∀ (ws : List Bool) (q : Bool), ext (xit t ws q) q = Si t (ext ws q) := by
  induction t with
  | zero => intro ws q; rfl
  | succ t ih =>
    intro ws q
    show ext (xit t (x102 ws q) q) q = S (Si t (ext ws q))
    rw [ih, ext_x102, Si_S]

theorem length_xit (t : Nat) : ∀ (ws : List Bool) (q : Bool), (xit t ws q).length = ws.length := by
  induction t with
  | zero => intro ws q; rfl
  | succ t ih => intro ws q; show (xit t (x102 ws q) q).length = _; rw [ih, length_x102]

/-- **The closed form.**  Word `i` after `t` epochs is the XOR, over the `k ≤ t` with `C(t, k)` odd, of word `i + k` of
the start (`q` just after the end, `x` beyond). -/
theorem closed_form (ws : List Bool) (q : Bool) (t i : Nat) (hi : i < ws.length) :
    (xit t ws q).getD i false = xsum (t + 1) (fun k => ext ws q (i + k) && disj k (t - k)) := by
  rw [← ext_lt (xit t ws q) q i (by rw [length_xit]; exact hi), ext_xit, Si_cf]
  rfl

/-! ## A gap of `x`s -/

theorem xsum_single (f : Nat → Bool) (m : Nat) (h : ∀ k, k ≠ m → f k = false) :
    ∀ N, xsum N f = (decide (m < N) && f m) := by
  intro N
  induction N with
  | zero => simp [xsum]
  | succ N ih =>
    show bne (xsum N f) (f N) = _
    rw [ih]
    by_cases e : N = m
    · subst e
      have a1 : decide (N < N) = false := by simp
      have a2 : decide (N < N + 1) = true := by simp
      rw [a1, a2]; cases f N <;> rfl
    · rw [h N e]
      have : decide (m < N + 1) = decide (m < N) := by
        by_cases hm : m < N
        · simp [hm]; omega
        · simp [hm]; omega
      rw [this]; simp

theorem ext_replicate (n : Nat) : ∀ j, ext (List.replicate n false) true j = (j == n) := by
  induction n with
  | zero => intro j; cases j <;> rfl
  | succ n ih =>
    intro j
    cases j with
    | zero => rfl
    | succ j => show ext (List.replicate n false) true j = (j + 1 == n + 1); rw [ih]; simp

/-- **A gap of `n` `x`s with `y` after it.**  After `t` epochs word `i` is `y` iff `n - i ≤ t` and `n - i`, `t - (n - i)`
share no binary 1 (`C(t, n - i)` odd). -/
theorem allx (n t i : Nat) (hi : i < n) :
    (xit t (List.replicate n false) true).getD i false = (decide (n - i ≤ t) && disj (n - i) (t - (n - i))) := by
  rw [closed_form _ true t i (by simp; exact hi)]
  rw [xsum_single _ (n - i) (fun k hk => by
    rw [ext_replicate]
    have : (i + k == n) = false := by simp; omega
    rw [this]; rfl) (t + 1)]
  rw [ext_replicate]
  have e : (i + (n - i) == n) = true := by simp; omega
  rw [e]
  have : decide (n - i < t + 1) = decide (n - i ≤ t) := by
    by_cases h : n - i ≤ t
    · simp [h]; omega
    · simp [h]; omega
  rw [this, Bool.true_and]

end H696
