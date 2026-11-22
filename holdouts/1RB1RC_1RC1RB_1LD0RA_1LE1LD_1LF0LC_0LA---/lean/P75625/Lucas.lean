-- Copied by holdouts/1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/py/port_mirror.py from
-- holdouts/1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/lean/Lucas.lean, imports renamed; do not edit by hand.
import P75625.Pascal

/-!
# The zone after `j` bounces, in closed form (Lucas' theorem mod 2)

`Pascal.lean` proves that a bounce maps the zone `w` to `tmap w`.  Here `tmap` is solved.

* Flip the nearest letter: `flip (tmap w) = 0 :: runningXOR (flip w)` (`flip_tmap`).  So after flipping, a bounce is
  "running XOR, then shift by one": the space-time diagram `E` obeys Pascal's rule
  `E (j+1) (i+1) = E (j+1) i xor E j i` (`diagram`).
* Pascal's rule mod 2 is solved by Lucas' theorem: `C(a + b, a)` is odd iff `a` and `b` have no binary 1 in the same
  place.  `disj a b` is that test, and `pascal_rule` proves that it obeys Pascal's rule.
* `closed_form`: letter `i` (counted from the right end, from 0) of `flip (tmap^j w)` is
  `XOR over k of d k ∧ Q j (i - k)`, where `d` is `flip w` and `Q (j+1) n` says `n ≥ j + 1` and the binary digits of `j` and
  `n - j - 1` are disjoint, i.e. `C(n - 1, j)` is odd.

Everything is for any word `w`; no step of the machine is involved here.
-/

namespace H75625

/-- Flip the nearest letter of a word. -/
def flip : List Bool → List Bool
  | [] => []
  | a :: ws => (!a) :: ws

theorem flip_tmap (ws : List Bool) : flip (tmap ws) = false :: sx false (flip ws) := by
  cases ws with
  | nil => rfl
  | cons a ws => cases a <;> rfl

theorem length_sx (q : Bool) (ws : List Bool) : (sx q ws).length = ws.length := by
  induction ws generalizing q with
  | nil => rfl
  | cons a ws ih => simp [sx, ih]

theorem length_flip (ws : List Bool) : (flip ws).length = ws.length := by
  cases ws <;> rfl

theorem length_tmap (ws : List Bool) : (tmap ws).length = ws.length + 1 := by
  simp [tmap, length_sx]

theorem titer_succ' (j : Nat) (ws : List Bool) : titer (j + 1) ws = tmap (titer j ws) := by
  induction j generalizing ws with
  | zero => rfl
  | succ j ih => show titer (j + 1) (tmap ws) = _; rw [ih]; rfl

theorem length_titer (j : Nat) (ws : List Bool) : (titer j ws).length = ws.length + j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [titer_succ', length_tmap, ih]; omega

/-- The running XOR, cell by cell. -/
theorem sx_zero (q a : Bool) (ws : List Bool) : (sx q (a :: ws)).getD 0 false = bne q a := rfl

theorem sx_succ (ws : List Bool) : ∀ (q : Bool) (i : Nat), i + 1 < ws.length →
    (sx q ws).getD (i + 1) false = bne ((sx q ws).getD i false) (ws.getD (i + 1) false) := by
  induction ws with
  | nil => intro q i h; simp at h
  | cons a ws ih =>
    intro q i h
    cases ws with
    | nil => simp at h
    | cons b ws' =>
      cases i with
      | zero => rfl
      | succ i =>
        have h' : i + 1 < (b :: ws').length := by simp at h ⊢; omega
        exact ih (bne q a) i h'

/-! ## The space-time diagram -/

/-- Pascal's rule with a seed row `d`: row `j`, column `i` (columns counted from the right end). -/
def E (d : Nat → Bool) : Nat → Nat → Bool
  | 0, i => d i
  | _ + 1, 0 => false
  | j + 1, i + 1 => bne (E d (j + 1) i) (E d j i)

/-- **The zone after `j` bounces is row `j` of the diagram** (after flipping its nearest letter), in every column the
zone has. -/
theorem diagram (ws : List Bool) (j : Nat) : ∀ i, i < ws.length + j →
    (flip (titer j ws)).getD i false = E (fun k => (flip ws).getD k false) j i := by
  induction j with
  | zero => intro i _; simp [titer, E]
  | succ j ih =>
    have hlen : (flip (titer j ws)).length = ws.length + j := by rw [length_flip, length_titer]
    -- the running XOR of row j is row j + 1, one column further
    have row : ∀ i, i < ws.length + j →
        (sx false (flip (titer j ws))).getD i false = E (fun k => (flip ws).getD k false) (j + 1) (i + 1) := by
      intro i
      induction i with
      | zero =>
        intro h
        rw [← hlen] at h
        cases hX : flip (titer j ws) with
        | nil => rw [hX] at h; simp at h
        | cons a t =>
          have h0 := ih 0 (by omega)
          rw [hX] at h0
          simp only [E]
          rw [← h0]; rfl
      | succ i ihi =>
        intro h
        rw [sx_succ _ false i (by omega), ihi (by omega), ih (i + 1) (by omega)]
        simp only [E]
    intro i hi
    rw [titer_succ', flip_tmap]
    cases i with
    | zero => simp [E]
    | succ i => exact row i (by omega)

/-! ## Lucas' theorem mod 2 -/

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

/-! ## The closed form -/

/-- `Q j n`: the seed's contribution `n` columns to its left in row `j`.  `Q (j+1) n` is "C(n - 1, j) is odd", i.e.
`n ≥ j + 1` and `j`, `n - j - 1` have disjoint binary digits. -/
def Q : Nat → Nat → Bool
  | 0, n => n == 0
  | j + 1, n => decide (j + 1 ≤ n) && disj j (n - j - 1)

theorem Q_zero (j : Nat) : Q (j + 1) 0 = false := by simp [Q]

theorem Q_rule (j m : Nat) : Q (j + 1) (m + 1) = bne (Q (j + 1) m) (Q j m) := by
  cases j with
  | zero => cases m <;> simp [Q, disj_zero_left]
  | succ j =>
    simp only [Q]
    by_cases h1 : m < j + 1
    · have a1 : decide (j + 1 + 1 ≤ m + 1) = false := by simp; omega
      have a2 : decide (j + 1 + 1 ≤ m) = false := by simp; omega
      have a3 : decide (j + 1 ≤ m) = false := by simp; omega
      rw [a1, a2, a3]; rfl
    · by_cases h2 : m = j + 1
      · subst h2
        have a1 : decide (j + 1 + 1 ≤ j + 1 + 1) = true := by simp
        have a2 : decide (j + 1 + 1 ≤ j + 1) = false := by simp
        have a3 : decide (j + 1 ≤ j + 1) = true := by simp
        rw [a1, a2, a3]
        simp [disj_zero_right]
      · have a1 : decide (j + 1 + 1 ≤ m + 1) = true := by simp; omega
        have a2 : decide (j + 1 + 1 ≤ m) = true := by simp; omega
        have a3 : decide (j + 1 ≤ m) = true := by simp; omega
        rw [a1, a2, a3]
        simp only [Bool.true_and]
        have e1 : m + 1 - (j + 1) - 1 = m - j - 1 := by omega
        have e2 : m - (j + 1) - 1 = m - j - 1 - 1 := by omega
        have e3 : m - j - 1 = m - j - 1 := rfl
        rw [e1, e2]
        exact pascal_rule (j + 1) (m - j - 1) (by omega) (by omega)

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

/-- The closed form: row `j`, column `i` is the XOR over the seed's cells `k ≤ i` of `d k ∧ Q j (i - k)`. -/
def G (d : Nat → Bool) (j i : Nat) : Bool := xsum (i + 1) (fun k => d k && Q j (i - k))

theorem G_row0 (d : Nat → Bool) (i : Nat) : G d 0 i = d i := by
  have h : ∀ n, n ≤ i → xsum n (fun k => d k && Q 0 (i - k)) = false := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      simp only [xsum]
      rw [ih (by omega)]
      have : (i - n == 0) = false := by simp; omega
      simp [Q, this]
  unfold G
  simp only [xsum]
  rw [h i (Nat.le_refl i)]
  simp [Q]

theorem E_eq_G (d : Nat → Bool) (j : Nat) : ∀ i, E d j i = G d j i := by
  induction j with
  | zero => intro i; rw [G_row0]; simp [E]
  | succ j ih =>
    intro i
    induction i with
    | zero => simp [E, G, xsum, Q_zero]
    | succ i ihi =>
      simp only [E]
      rw [ihi, ih i]
      unfold G
      show _ = bne (xsum (i + 1) (fun k => d k && Q (j + 1) (i + 1 - k))) (d (i + 1) && Q (j + 1) (i + 1 - (i + 1)))
      rw [Nat.sub_self, Q_zero, Bool.and_false]
      rw [xsum_congr (i + 1) (fun k => d k && Q (j + 1) (i + 1 - k))
            (fun k => bne (d k && Q (j + 1) (i - k)) (d k && Q j (i - k)))
            (fun k hk => by
              have e : i + 1 - k = (i - k) + 1 := by omega
              rw [e, Q_rule]
              cases d k <;> rfl)]
      rw [xsum_bne]
      cases xsum (i + 1) (fun k => d k && Q (j + 1) (i - k)) <;>
        cases xsum (i + 1) (fun k => d k && Q j (i - k)) <;> rfl

/-- **The zone after `j` bounces, in closed form.**  Count letters from the right end of the zone (0 is the letter
next to the frozen tape) and flip letter 0 (`flip`); write `d` for the flipped starting word.  Then letter `i` of the
flipped zone after `j` bounces is the XOR, over `k ≤ i`, of `d k ∧ Q j (i - k)`: by Lucas' theorem, cell `k` of the start
reaches cell `i` after `j ≥ 1` bounces iff `i - k ≥ j` and the binary digits of `j - 1` and `i - k - j` are disjoint. -/
theorem closed_form (ws : List Bool) (j i : Nat) (hi : i < ws.length + j) :
    (flip (titer j ws)).getD i false = G (fun k => (flip ws).getD k false) j i := by
  rw [diagram ws j i hi, E_eq_G]

end H75625
