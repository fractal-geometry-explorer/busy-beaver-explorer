import Rules

/-!
# 1RB0RF_1LC0RC_0LD1LC_1RE1LB_1RF---_1LE1RA: the transfer and the doubling chain at the left end

`G` = `0^inf 1 1 1 0 1 0 1 1 0 C> 0` is the left end of the tape with the head in C.

* `Tr j n R` = `G (10)^(2j+1) 1^(2n+1) R`.  The transfer (`transfer`, `Rules.lean`) moves two ones into two more
  copies of `10`: `Tr j (n+1) R -> Tr (j+1) n R` in 28j+64 steps, so `transfer_n`: `Tr j n R -> Tr (j+n) 0 R` in
  `cost j n = n (28j + 14n + 50)` steps (`cost_eq`) - quadratic in the block, which is where the machine spends
  nearly all of its time.
* `E n R` = `G 10 1^(2n+2) (10)^3 1^5 0 R`.  When the item `1^7 0` follows (`chain7`):
  `E n (1^7 0 R) -> E (2n+7) R`, that is, the block of x = 2n+2 ones becomes 2x+12 ones and the item is used up.
  `chain`: c items in a row give c doublings.  This is how the giant blocks of ones arise.

Nothing here says which items the sweeps of the rest of the tape produce, so the halting problem of the machine is
not reduced.
-/

namespace H49956

open TM

/-- The left end of the tape (cells left of the head, nearest first): `0^inf 1 1 1 0 1 0 1 1 0`. -/
def GL : Tape :=
  cons false (cons true (cons true (cons false (cons true (cons false (cons true (cons true (cons true blank))))))))

/-- `G (10)^(2j+1) 1^(2n+1) R`. -/
def Tr (j n : Nat) (R : Tape) : Config :=
  ⟨GL, cons false (rep j [true, false, true, false] (cons true (cons false (rep n [true, true] (cons true R))))), .C⟩

theorem rot (j : Nat) (s : Tape) :
    cons true (rep j [false, true, false, true] s) = rep j [true, false, true, false] (cons true s) :=
  rep_rotate j [true] [false, true, false, true] [true, false, true, false] rfl s

theorem one_rot (n : Nat) (s : Tape) : cons true (rep n [true, true] s) = rep n [true, true] (cons true s) :=
  rep_rotate n [true] [true, true] [true, true] rfl s

/-- One transfer. -/
theorem transfer1 (j n : Nat) (R : Tape) : steps (28 * j + 64) (Tr j (n + 1) R) = some (Tr (j + 1) n R) := by
  have h := transfer j (rep n [true, true] R)
  rw [rot, one_rot] at h
  exact h

/-- The number of steps of n transfers starting from 2j+1 copies of `10`. -/
def cost : Nat → Nat → Nat
  | _, 0 => 0
  | j, n + 1 => (28 * j + 64) + cost (j + 1) n

/-- All the ones but one are transferred. -/
theorem transfer_n (n : Nat) : ∀ (j : Nat) (R : Tape), steps (cost j n) (Tr j n R) = some (Tr (j + n) 0 R) := by
  induction n with
  | zero => intro j R; rfl
  | succ n ih =>
    intro j R
    have h := steps_seq trans (transfer1 j n R) (ih (j + 1) R)
    have e : j + 1 + n = j + (n + 1) := by omega
    rw [e] at h
    exact h

theorem cost_eq (n : Nat) : ∀ j : Nat, cost j n = n * (28 * j + 14 * n + 50) := by
  induction n with
  | zero => intro j; simp [cost]
  | succ n ih =>
    intro j
    rw [cost, ih (j + 1)]
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one]
    have e1 : n * (28 * j) = 28 * (n * j) := by rw [Nat.mul_left_comm]
    have e2 : n * (14 * n) = 14 * (n * n) := by rw [Nat.mul_left_comm]
    rw [e1, e2]
    generalize n * j = a
    generalize n * n = b
    omega

/-- The word `(10)^3 1^5 0` after the block of ones. -/
def S (R : Tape) : Tape :=
  cons true (cons false (cons true (cons false (cons true (cons false
    (cons true (cons true (cons true (cons true (cons true (cons false R)))))))))))

/-- `G 10 1^(2n+2) (10)^3 1^5 0 R`. -/
def E (n : Nat) (R : Tape) : Config := Tr 0 n (cons true (S R))

theorem rep4 (n : Nat) (s : Tape) : rep n [true, true, true, true] s = rep (2 * n) [true, true] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
    rw [e, rep_succ, rep_succ, rep_succ, ih]
    rfl

/-- One doubling: the block of 2n+2 ones becomes 4n+16 ones, the item `1^7 0` is used up. -/
theorem chain7 (n : Nat) (R : Tape) :
    steps (cost 0 n + (38 * n + 184)) (E n (rep 1 [true, true, true, true, true, true, true, false] R))
      = some (E (2 * n + 7) R) := by
  have h1 := transfer_n n 0 (cons true (S (rep 1 [true, true, true, true, true, true, true, false] R)))
  have h2 := double7 n R
  rw [rep4] at h2
  simp only [one_rot] at h2
  have e : (E (2 * n + 7) R) = ⟨GL, cons false (cons true (cons false (rep (2 * n) [true, true]
      (rep 7 [true, true] (cons true (cons true (S R))))))), .C⟩ := by
    show Tr 0 (2 * n + 7) (cons true (S R)) = _
    unfold Tr
    rw [rep_add]
    rfl
  rw [e]
  have e0 : 0 + n = n := by omega
  rw [e0] at h1
  have h2' : steps (38 * n + 184) (Tr n 0 (cons true (S (rep 1 [true, true, true, true, true, true, true, false] R))))
      = some ⟨GL, cons false (cons true (cons false (rep (2 * n) [true, true]
      (rep 7 [true, true] (cons true (cons true (S R))))))), .C⟩ := h2
  exact steps_seq trans h1 h2'

/-- c doublings of n -> 2n+7. -/
def dbl : Nat → Nat → Nat
  | 0, n => n
  | c + 1, n => dbl c (2 * n + 7)

/-- A chain: c items `1^7 0` in a row give c doublings. -/
theorem chain (c : Nat) : ∀ (n : Nat) (R : Tape),
    ∃ s, steps s (E n (rep c [true, true, true, true, true, true, true, false] R)) = some (E (dbl c n) R) := by
  induction c with
  | zero => intro n R; exact ⟨0, rfl⟩
  | succ c ih =>
    intro n R
    obtain ⟨s, hs⟩ := ih (2 * n + 7) R
    exact ⟨_, steps_seq trans (chain7 n (rep c [true, true, true, true, true, true, true, false] R)) hs⟩

theorem dbl_eq (c : Nat) : ∀ n : Nat, dbl c n + 7 = 2 ^ c * (n + 7) := by
  induction c with
  | zero => intro n; simp [dbl]
  | succ c ih =>
    intro n
    rw [dbl, ih (2 * n + 7), Nat.pow_succ]
    have e : 2 * n + 7 + 7 = 2 * (n + 7) := by omega
    rw [e, Nat.mul_assoc]

end H49956
