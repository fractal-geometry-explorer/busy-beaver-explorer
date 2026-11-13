import Rules

/-!
# The right-end regime as a theorem for every list of blocks

Read left to right, the tape in this regime is

    (10)^(a+2) 1 (10)^(k_n+2) ... 1 (10)^(k_1+2) (1101010)^(m+1) A>0

with blank tape on both sides: a first block, any number of blocks `1 (10)^(k+2)` (every block has at least two
`10`s), and a tail of `m + 1` words `1101010`. `T a ks m` is this configuration, with `ks = [k_1, ..., k_n]` listed
from the right (the order in which the head meets them going left).

One round trip of the head takes `T (a + 1) ks m` to `T a ks (m + 1)` (`trip`), whatever the list `ks` is: the first
block loses one `10` and the tail gains one word. Iterated, `T (a + j) ks m` reaches `T a ks (m + j)` (`trip_iter`).
The pieces are the generated rules in `Rules.lean`; here they are put together by induction on the list.
-/

namespace H14847

open TM

/-- `1101010` read from the right (the left tape is stored nearest cell first). -/
def w7 : List Bool := [false, true, false, true, false, true, true]

/-- The blocks `1 (10)^(k+2)`, listed from the right, in front of the tape `s` (stored nearest cell first). -/
def BL : List Nat → Tape → Tape
  | [], s => s
  | k :: ks, s => rep (k + 2) [false, true] (cons true (BL ks s))

/-- A block as the left-moving head leaves it: `(10)^k 0 1 1 0 0`. -/
def U (k : Nat) (s : Tape) : Tape :=
  rep k [true, false] (cons false (cons true (cons true (cons false (cons false s)))))

/-- The blocks after the left-moving pass, in front of `s` (the last one met is nearest the head). -/
def UR : List Nat → Tape → Tape
  | [], s => s
  | k :: ks, s => UR ks (U k s)

/-- The cells `0 0 1 1 0 0` in front of the head when it moves right over a block. -/
def PF (s : Tape) : Tape :=
  cons false (cons false (cons true (cons true (cons false (cons false s)))))

/-- The regime's configuration: first block `(10)^(a+2)`, blocks `ks` (from the right), tail `(1101010)^(m+1)`. -/
def T (a : Nat) (ks : List Nat) (m : Nat) : Config :=
  ⟨rep (m + 1) w7 (BL ks (rep (a + 2) [false, true] blank)), blank, .A⟩

/-- Moving left over all the blocks `ks`. -/
theorem passL : ∀ (ks : List Nat) (s R : Tape),
    ∃ n, steps n ⟨cons true (BL ks s), cons true R, .A⟩ = some ⟨cons true s, cons true (UR ks R), .A⟩
  | [], s, R => ⟨0, rfl⟩
  | k :: ks, s, R => by
    obtain ⟨n, hn⟩ := passL ks s (U k R)
    exact ⟨2 * k + 5 + n, steps_seq trans (crossL k (cons true (BL ks s)) R) hn⟩

theorem absorb2 (k : Nat) (s : Tape) :
    rep k [false, true] (cons false (cons true (cons false (cons true (cons true s))))) =
      rep (k + 2) [false, true] (cons true s) :=
  (rep_app_comm k [false, true] (app [false, true] (cons true s))).trans (rep_app_comm (k + 1) [false, true] (cons true s))

/-- Moving right over all the blocks: each comes back as `1 (10)^(k+2)`. -/
theorem passR : ∀ (ks : List Nat) (L R : Tape),
    ∃ n, steps n ⟨L, PF (UR ks R), .A⟩ = some ⟨BL ks L, PF R, .A⟩
  | [], L, R => ⟨0, rfl⟩
  | k :: ks, L, R => by
    obtain ⟨n, hn⟩ := passR ks L (U k R)
    have h := crossR k (BL ks L) (cons false (cons true (cons true (cons false (cons false R)))))
    rw [absorb2] at h
    exact ⟨n + (2 * k + 15), steps_seq trans hn h⟩

theorem tail_rot (m : Nat) (s : Tape) :
    cons false (cons true (cons false (cons true (cons false (cons true
      (rep m [true, false, true, false, true, false, true] (cons true s))))))) = rep (m + 1) w7 s := by
  rw [show cons false (cons true (cons false (cons true (cons false (cons true
      (rep m [true, false, true, false, true, false, true] (cons true s))))))) =
      app [false, true, false, true, false, true] (rep m [true, false, true, false, true, false, true] (cons true s))
      from rfl,
    rep_rotate m [false, true, false, true, false, true] [true, false, true, false, true, false, true] w7 rfl,
    show app [false, true, false, true, false, true] (cons true s) = app w7 s from rfl, rep_app_comm]

/-- One round trip: the first block loses a `10`, the tail gains a word `1101010` (kernel). -/
theorem trip (a : Nat) (ks : List Nat) (m : Nat) : ∃ n, steps n (T (a + 1) ks m) = some (T a ks (m + 1)) := by
  let R0 := rep (m + 1) [true, false, false, true, true, false, false] (cons true blank)
  have h1 := rightEnd m (BL ks (rep (a + 1 + 2) [false, true] blank))
  obtain ⟨n2, h2⟩ := passL ks (rep (a + 1 + 2) [false, true] blank) R0
  have h3 := crossL (a + 1) blank (UR ks R0)
  have h4 := turnL (U (a + 1) (UR ks R0))
  have h5 := crossR0 (a + 1) (cons false (cons true blank))
    (cons false (cons true (cons true (cons false (cons false (UR ks R0))))))
  obtain ⟨n6, h6⟩ := passR ks (rep (a + 1) [false, true] (cons false (cons true blank))) R0
  have h7 := rightEnd2 (m + 1) (BL ks (rep (a + 1) [false, true] (cons false (cons true blank))))
  rw [tail_rot] at h7
  rw [show rep (a + 1) [false, true] (cons false (cons true blank)) = rep (a + 2) [false, true] blank from
    rep_app_comm (a + 1) [false, true] blank] at h5 h6 h7
  exact ⟨_, steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4
    (steps_seq trans h5 (steps_seq trans h6 h7)))))⟩

/-- `j` round trips: `T (a + j) ks m` reaches `T a ks (m + j)` (kernel). -/
theorem trip_iter (ks : List Nat) : ∀ (j a m : Nat), ∃ n, steps n (T (a + j) ks m) = some (T a ks (m + j))
  | 0, a, m => ⟨0, rfl⟩
  | j + 1, a, m => by
    obtain ⟨n1, h1⟩ := trip (a + j) ks m
    obtain ⟨n2, h2⟩ := trip_iter ks j a (m + 1)
    rw [show a + (j + 1) = a + j + 1 by omega, show m + (j + 1) = m + 1 + j by omega]
    exact ⟨n1 + n2, steps_seq trans h1 h2⟩

end H14847
