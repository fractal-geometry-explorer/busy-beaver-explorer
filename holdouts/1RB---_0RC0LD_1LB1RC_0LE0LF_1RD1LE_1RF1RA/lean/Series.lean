import Blocks

/-!
# 1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA: the zigzag in one step, and what small blocks at the left end do

Consequences of the block map `next` of `Blocks.lean`, by computation with it.

* `zig`: the zigzag.  From `E (i :: L) (m + 2 + 3t :: 0 :: j :: R)` the block map makes `t` trips of three frames
  each and reaches `E (i + 2t :: L) (m + 2 :: 0 :: j + t :: R)`: the block being cut loses 3 cells per trip, the block
  on its left gains 2, the block behind the double 0 gains 1.
* `halts_of_15`: if the run from blank tape ever reaches `E [] (15 :: 0 :: j :: R)` (the zigzag at the left end of
  the tape, on a block of exactly 15 cells), the machine halts.  `critical_mid` is the same event away from the
  left end: a block of `m` = 3, 6, 9 or 12 cells with `10 - 2m/3` cells on its left.
* `never_halts_of_2`, `never_halts_of_3`: if the run ever reaches `E [] (2 :: 0 :: j :: R)` or
  `E [] (3 :: 0 :: j :: R)`, the machine never halts: the frame `E [] (2 :: 0 :: j :: R)` comes back with `j + 1`
  for ever.

None of these frames has been seen in the run (see the README); whether one is ever reached is open.
-/

namespace H15414

open TM

theorem iterF_add (a b : Nat) (p : Ph) : iterF next (a + b) p = (iterF next a p).bind (iterF next b) := by
  induction a generalizing p with
  | zero => simp [iterF]
  | succ a ih =>
    have : a + 1 + b = (a + b) + 1 := by omega
    rw [this]
    simp only [iterF]
    cases next p with
    | none => rfl
    | some q => simp only [Option.bind_some]; exact ih q

theorem iterF_prefix {a b : Nat} {p q : Ph} (h : iterF next (a + b) p = some q) : ∃ r, iterF next a p = some r := by
  rw [iterF_add] at h
  cases h' : iterF next a p with
  | none => rw [h'] at h; cases h
  | some r => exact ⟨r, rfl⟩

/-- One trip of the zigzag. -/
theorem zig1 (i : Nat) (L : List Nat) (m j : Nat) (R : List Nat) :
    iterF next 3 (.E (i :: L) ((m + 5) :: 0 :: j :: R)) = some (.E ((i + 2) :: L) ((m + 2) :: 0 :: (j + 1) :: R)) := rfl

/-- **The zigzag**: `t` trips at once. -/
theorem zig : ∀ (t i : Nat) (L : List Nat) (m j : Nat) (R : List Nat),
    iterF next (3 * t) (.E (i :: L) ((m + 2 + 3 * t) :: 0 :: j :: R))
      = some (.E ((i + 2 * t) :: L) ((m + 2) :: 0 :: (j + t) :: R))
  | 0, i, L, m, j, R => rfl
  | t + 1, i, L, m, j, R => by
    have e1 : 3 * (t + 1) = 3 + 3 * t := by omega
    have e2 : m + 2 + 3 * (t + 1) = (m + 3 * t) + 5 := by omega
    rw [e2, e1, iterF_add, zig1, Option.bind_some]
    have e3 : m + 3 * t + 2 = m + 2 + 3 * t := by omega
    rw [e3, zig t (i + 2) L m (j + 1) R]
    have e4 : i + 2 + 2 * t = i + 2 * (t + 1) := by omega
    have e5 : j + 1 + t = j + (t + 1) := by omega
    rw [e4, e5]

/-- The first trip at the left end of the tape (nothing left of the head). -/
theorem zig1_end (m j : Nat) (R : List Nat) :
    iterF next 3 (.E [] ((m + 5) :: 0 :: j :: R)) = some (.E [2] ((m + 2) :: 0 :: (j + 1) :: R)) := rfl

/-- A block of exactly 15 cells cut at the left end of the tape leads to a critical frame. -/
theorem critical_15 (j : Nat) (R : List Nat) :
    ∃ k p, iterF next k (.E [] (15 :: 0 :: j :: R)) = some p ∧ Critical p :=
  ⟨23, .C [2, 11, 0] ((j + 4) :: R), rfl, by show (2:Nat) = 2 ∧ 1 ≤ j + 4; omega⟩

/-- The same event away from the left end: a block of 9 cells with 4 on its left, 12 with 2, 6 with 6. -/
theorem critical_mid (j : Nat) (L R : List Nat) :
    (∃ k p, iterF next k (.E (4 :: L) (9 :: 0 :: j :: R)) = some p ∧ Critical p) ∧
    (∃ k p, iterF next k (.E (2 :: L) (12 :: 0 :: j :: R)) = some p ∧ Critical p) ∧
    (∃ k p, iterF next k (.E (6 :: L) (6 :: 0 :: j :: R)) = some p ∧ Critical p) :=
  ⟨⟨17, .C (2 :: (hd L + 11) :: hd (tl L) :: tl (tl L)) ((j + 2) :: R), rfl, by show (2:Nat) = 2 ∧ 1 ≤ j + 2; omega⟩,
   ⟨20, .C (2 :: (hd L + 11) :: hd (tl L) :: tl (tl L)) ((j + 3) :: R), rfl, by show (2:Nat) = 2 ∧ 1 ≤ j + 3; omega⟩,
   ⟨14, .C (2 :: (hd L + 11) :: hd (tl L) :: tl (tl L)) ((j + 1) :: R), rfl, by show (2:Nat) = 2 ∧ 1 ≤ j + 1; omega⟩⟩

/-- At the left end a block of 2 cells is never used up: three frames later it is there again. -/
theorem loop_2 (j : Nat) (R : List Nat) :
    iterF next 3 (.E [] (2 :: 0 :: j :: R)) = some (.E [] (2 :: 0 :: (j + 1) :: R)) := rfl

theorem loop_2_iter : ∀ (q j : Nat) (R : List Nat),
    iterF next (3 * q) (.E [] (2 :: 0 :: j :: R)) = some (.E [] (2 :: 0 :: (j + q) :: R))
  | 0, j, R => rfl
  | q + 1, j, R => by
    have e1 : 3 * (q + 1) = 3 + 3 * q := by omega
    rw [e1, iterF_add, loop_2, Option.bind_some, loop_2_iter q (j + 1) R]
    have e2 : j + 1 + q = j + (q + 1) := by omega
    rw [e2]

theorem loop_2_defined (n j : Nat) (R : List Nat) : ∃ p, iterF next n (.E [] (2 :: 0 :: j :: R)) = some p := by
  have h := loop_2_iter n j R
  have e : 3 * n = n + 2 * n := by omega
  rw [e] at h
  exact iterF_prefix h

/-- If the block map is defined for ever from a frame of the run, the machine does not halt. -/
theorem never_halts_of_defined {k : Nat} {p0 : Ph} (h0 : iterF next k start = some p0)
    (hall : ∀ n, ∃ p, iterF next n p0 = some p) : ¬ HaltsFromBlank := by
  rw [halts_iff]
  rintro ⟨k', p, hp, hn⟩
  have hs : iterF next (k' + 1) start = none := by rw [iterF_succ next k' start p hp, hn]
  rcases Nat.lt_or_ge k' k with hlt | hge
  · have e : k = (k' + 1) + (k - (k' + 1)) := by omega
    rw [e, iterF_add, hs] at h0
    cases h0
  · have e : k' + 1 = k + (k' + 1 - k) := by omega
    rw [e, iterF_add, h0, Option.bind_some] at hs
    obtain ⟨r, hr⟩ := hall (k' + 1 - k)
    rw [hr] at hs
    cases hs

/-- **If the run ever cuts a block of exactly 2 cells at the left end of the tape, the machine never halts.** -/
theorem never_halts_of_2 {k j : Nat} {R : List Nat} (h : iterF next k start = some (.E [] (2 :: 0 :: j :: R))) :
    ¬ HaltsFromBlank :=
  never_halts_of_defined h (fun n => loop_2_defined n j R)

/-- The same for a block of exactly 3 cells: two frames later it is a block of 2. -/
theorem never_halts_of_3 {k j : Nat} {R : List Nat} (h : iterF next k start = some (.E [] (3 :: 0 :: j :: R))) :
    ¬ HaltsFromBlank := by
  have h2 : iterF next (k + 2) start = some (.E [] (2 :: 0 :: 1 :: j :: R)) := by
    rw [iterF_add, h, Option.bind_some]; rfl
  exact never_halts_of_2 h2

/-- **If the run ever cuts a block of exactly 15 cells at the left end of the tape, the machine halts.** -/
theorem halts_of_15 {k j : Nat} {R : List Nat} (h : iterF next k start = some (.E [] (15 :: 0 :: j :: R))) :
    HaltsFromBlank := by
  rw [halts_iff_critical]
  obtain ⟨k', p, hp, hc⟩ := critical_15 j R
  exact ⟨k + k', p, by rw [iterF_add, h, Option.bind_some, hp], hc⟩

end H15414
