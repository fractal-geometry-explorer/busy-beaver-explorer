import Counter

/-! # Building a wall: the copy loop at the left end

When the counter's walk meets a level `0 (10)^X` that has a single pair to its left, the head goes on into the left
end of the tape and then shuttles between the left end and that level: each round moves one pair out of the level
and adds two to the first block, the blocks in between unchanged.  At the start of each round the head is in state
C at the left end, with blank tape to its left and, to its right,

    0 (10)^(2a+1)  0 (10)^(2 t₁ + 2)  …  0 (10)^(2 tₘ + 2)  0 0 (10)^X  R

(`Rd a ts X R`).  `wall_round` proves one round, `Rd a ts (x+1) R → Rd (a+1) ts x R`, for every `a`, every list of
blocks `ts`, every `x` and any tape `R`; `wall_loop` iterates it any number of times.  The moves are the pieces
`wall_start`, `wall_right`, `wall_turn`, `wall_left`, `wall_end` of `Rules.lean`; the rest is induction on the list
of blocks and tape algebra.  Hand-written; kernel only. -/

namespace BB6e
open TM

/-- A pair `10`, read from left to right (on the right of the head). -/
abbrev P' : List Bool := [true, false]
/-- Two pairs `0101` shifted by one cell. -/
abbrev Q0 : List Bool := [false, true, false, true]

/-- A block `0 (10)^(2t+2)` of the tape between the left end and the level being copied, on the right of the head
(the last pair written after the repeat). -/
def WB (t : Nat) (Z : Tape) : Tape := cons false (cons true (cons false (rep t Q' (cons true (cons false Z)))))

def WBs : List Nat → Tape → Tape
  | [], Z => Z
  | t :: ts, Z => WB t (WBs ts Z)

/-- The level being copied: `0 0 (10)^X`, then any tape. -/
def WX (X : Nat) (R : Tape) : Tape := cons false (cons false (rep X P' R))

/-- The tape right of the head at the start of a round: the first block `(10)^(2a+1)`, the blocks `ts`, the level. -/
def Rd (a : Nat) (ts : List Nat) (X : Nat) (R : Tape) : Tape :=
  cons false (rep a Q' (cons true (cons false (WBs ts (WX X R)))))

/-- A block after E crossed it, left of the head (read leftwards), its boundary marked. -/
def MK (t : Nat) (L : Tape) : Tape := rep t Q' (cons true (cons true (cons false (cons true (cons false L)))))

def MKs : List Nat → Tape → Tape
  | [], L => L
  | t :: ts, L => MKs ts (MK t L)

/-- A block after the head crossed it back to the left (right of the head). -/
def NB (t : Nat) (Z : Tape) : Tape := cons false (cons true (cons false (cons false (cons true (rep t Q0 Z)))))

def NBs : List Nat → Tape → Tape
  | [], Z => Z
  | t :: ts, Z => NB t (NBs ts Z)

/-! ## Tape algebra -/

theorem rot1 (n : Nat) (s : Tape) : cons true (rep n Q0 s) = rep n Q' (cons true s) :=
  rep_rotate n [true] Q0 Q' rfl s

theorem rot2 (n : Nat) (s : Tape) : cons true (cons false (rep n Q' s)) = rep n Q' (cons true (cons false s)) :=
  rep_rotate n P' Q' Q' rfl s

theorem nbs_wbs (ts : List Nat) (Y : Tape) :
    NBs ts (cons false (cons true (cons false Y))) = cons false (cons true (cons false (WBs ts Y))) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [NBs, WBs, NB, WB, ih]
    rw [rot1, ← rot2]

theorem wbs_head (ts : List Nat) (X : Nat) (R : Tape) : ∃ R', WBs ts (WX X R) = cons false R' := by
  cases ts with
  | nil => exact ⟨_, rfl⟩
  | cons t ts => exact ⟨_, rfl⟩

/-! ## One round -/

/-- E crosses the blocks `ts` to the right, marking each. -/
theorem wall_rightN (ts : List Nat) : ∀ L Y, ∃ n,
    steps n ⟨L, cons true (cons false (WBs ts Y)), .E⟩ = some ⟨MKs ts L, cons true (cons false Y), .E⟩ := by
  induction ts with
  | nil => intro L Y; exact ⟨0, rfl⟩
  | cons t ts ih =>
    intro L Y
    obtain ⟨n, hn⟩ := ih (MK t L) Y
    exact ⟨_, steps_seq trans (wall_right t L (cons true (cons false (WBs ts Y)))) hn⟩

/-- The head crosses the marked blocks `ts` back to the left, clearing the marks. -/
theorem wall_leftN (ts : List Nat) : ∀ L Z, ∃ n,
    steps n ⟨MKs ts L, cons false Z, .D⟩ = some ⟨L, cons false (NBs ts Z), .D⟩ := by
  induction ts with
  | nil => intro L Z; exact ⟨0, rfl⟩
  | cons t ts ih =>
    intro L Z
    obtain ⟨n, hn⟩ := ih (MK t L) Z
    exact ⟨_, steps_seq trans hn (wall_left t L (NBs ts Z))⟩

/-- One round of the copy loop: one pair from the level to the first block's two. -/
theorem wall_round (a : Nat) (ts : List Nat) (x : Nat) (R : Tape) :
    ∃ n, steps n ⟨blank, Rd a ts (x + 1) R, .C⟩ = some ⟨blank, Rd (a + 1) ts x R, .C⟩ := by
  obtain ⟨R', hR'⟩ := wbs_head ts (x + 1) R
  have h1 := wall_start a R'
  rw [← hR'] at h1
  obtain ⟨n2, h2⟩ := wall_rightN ts (rep a Q' (cons true blank)) (WX (x + 1) R)
  have h3 : steps 8 ⟨MKs ts (rep a Q' (cons true blank)), cons true (cons false (WX (x + 1) R)), .E⟩
      = some ⟨MKs ts (rep a Q' (cons true blank)), cons false (cons false (cons true (cons false (WX x R)))), .D⟩ :=
    wall_turn x _ R
  obtain ⟨n4, h4⟩ := wall_leftN ts (rep a Q' (cons true blank)) (cons false (cons true (cons false (WX x R))))
  have h5 := wall_end a (NBs ts (cons false (cons true (cons false (WX x R)))))
  rw [rot1] at h5
  have e : cons false (cons true (cons false (rep a Q' (cons true
      (NBs ts (cons false (cons true (cons false (WX x R))))))))) = Rd (a + 1) ts x R := by
    simp only [Rd, nbs_wbs]
    rw [rot2, rep_succ']
    rfl
  rw [e] at h5
  exact ⟨_, steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 h5)))⟩

/-- The copy loop: k rounds move k pairs from the level being copied to the first block's 2k. -/
theorem wall_loop (ts : List Nat) (x : Nat) (R : Tape) (k : Nat) : ∀ a,
    ∃ n, steps n ⟨blank, Rd a ts (x + k) R, .C⟩ = some ⟨blank, Rd (a + k) ts x R, .C⟩ := by
  induction k with
  | zero => intro a; exact ⟨0, rfl⟩
  | succ k ih =>
    intro a
    obtain ⟨n1, h1⟩ := wall_round a ts (x + k) R
    obtain ⟨n2, h2⟩ := ih (a + 1)
    rw [show a + 1 + k = a + (k + 1) by omega] at h2
    exact ⟨_, steps_seq trans h1 h2⟩

/-- The whole loop: a level of X pairs copied into the first block, `Rd a ts X R → Rd (a+X) ts 0 R`. -/
theorem wall_jump (a : Nat) (ts : List Nat) (X : Nat) (R : Tape) :
    ∃ n, steps n ⟨blank, Rd a ts X R, .C⟩ = some ⟨blank, Rd (a + X) ts 0 R, .C⟩ := by
  obtain ⟨n, h⟩ := wall_loop ts 0 R X a
  rw [Nat.zero_add] at h
  exact ⟨n, h⟩

/-! ## Normal form of tapes right of the head

For matching a tape as a symbolic run reaches it with `Rd`: constant counts are expanded, `(10)^(2n)` is written
`(1010)^n`, and literal cells are moved to the right of the repeats they can cross (`x (y x)^n = (x y)^n x`). -/

/-- Two repeats of one word commute (for `simp`, which uses it as an ordered rewrite). -/
theorem rep_swap (a b : Nat) (w : List Bool) (s : Tape) : rep a w (rep b w s) = rep b w (rep a w s) := by
  rw [← rep_add, ← rep_add, Nat.add_comm]

theorem rpq (n : Nat) (s : Tape) : rep (2 * n) P' s = rep n Q' s := rep_two_mul n P' s
theorem rpq0 (n : Nat) (s : Tape) : rep (2 * n) [false, true] s = rep n Q0 s := rep_two_mul n [false, true] s
theorem mv10 (n : Nat) (s : Tape) : cons false (rep n P' s) = rep n [false, true] (cons false s) :=
  rep_rotate n [false] P' [false, true] rfl s
theorem mv01 (n : Nat) (s : Tape) : cons true (rep n [false, true] s) = rep n P' (cons true s) :=
  rep_rotate n [true] [false, true] P' rfl s
theorem mvQ (n : Nat) (s : Tape) : cons false (rep n Q' s) = rep n Q0 (cons false s) :=
  rep_rotate n [false] Q' Q0 rfl s
theorem mvQ0 (n : Nat) (s : Tape) : cons true (rep n Q0 s) = rep n Q' (cons true s) := rot1 n s

/-- A borrow that turns on the tape `T` by any piece, as `counter_borrow_any`, with the piece's step count allowed
to depend on the tape to its right. -/
theorem counter_borrow_ex (c d : Nat) (zs : List (Nat × Nat)) {T X : Tape}
    (h : ∀ R : Tape, ∃ m, steps m ⟨T, W5 (cons false (cons true R)), .C⟩ = some ⟨F3 X, R, .C⟩)
    (hX : ∃ Y, X = cons false Y) :
    ∃ n, steps n ⟨lv false false (2 * c + 2) (2 * d + 2) (Zs zs (app Q T)), R0, .C⟩
      = some ⟨lv true true (2 * c + 3) (2 * d + 3) (Rs zs X), R0, .C⟩ := by
  obtain ⟨n1, h1⟩ := walk_all c d zs T
  obtain ⟨m, h2⟩ := h (JR zs (JbL c d))
  obtain ⟨n3, h3⟩ := sweepN zs (F3 X) (JbL c d)
  rw [sr_canon] at h3
  obtain ⟨Y, rfl⟩ := hX
  obtain ⟨Y', hY⟩ := rs_head zs Y
  have h4 : steps (4 * c + 4 * d + 11) ⟨F3 (cons false Y'), JbL c d, .C⟩ = some ⟨OL c d Y', R0, .C⟩ :=
    sweepLast c d Y'
  rw [ol_canon, ← hY] at h4
  exact ⟨_, steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4))⟩

end BB6e
