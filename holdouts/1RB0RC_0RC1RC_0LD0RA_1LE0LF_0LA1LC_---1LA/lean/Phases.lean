import Rules

/-!
# The two long phases of 1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA, any number of cycles

Written by hand on top of `Rules.lean` (`collect_raw`, `expand_raw`: one cycle each, generated with its proof by
`py/rules.py`).  Here the end configuration of a cycle is re-bracketed into the form of its start, and the cycles
are chained by induction.

Tape words: `W = 1011001` (the left block), `V = 110110` (two words of the blocks of three-cell words, which are
`011`, `110` or `101` depending on where one starts reading).
-/

namespace H65826

open TM

/-- The word of the left block. -/
abbrev W : List Bool := [true, false, true, true, false, false, true]
/-- Two three-cell words. -/
abbrev V : List Bool := [true, true, false, true, true, false]

/-- Right of the left block while collecting: `(101)^5 10 0110110 (110110)^a 000 (110110)^b 110`, that is
`(101)^5 10 (011)^(2a+2) 0000 (110)^(2b+1)`. -/
def colTail (a b : Nat) : Tape :=
  app [true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, false, true, true, false, true, true, false]
    (rep a V (app [false, false, false] (rep b V (app [true, true, false] blank))))

/-- Collecting, at the moment state E reaches the left end: `E> 0 (1011001)^p (101)^5 10 (011)^(2a+2) 0000
(110)^(2b+1)` on an otherwise blank tape. -/
def colCfg (p a b : Nat) : Config := ⟨blank, cons false (rep p W (colTail a b)), .E⟩

/-- One collecting cycle (two visits of the left end): two more words in the left block, two fewer three-cell
words in the middle block. -/
theorem collect2 (p a b : Nat) :
    steps (48 * a + 48 * b + 72 * p + 476) (colCfg (p + 1) (a + 1) (b + 1)) = some (colCfg (p + 3) a (b + 1)) := by
  have h := collect_raw a b p
  have e := rep_app_comm p W (colTail a (b + 1))
  show steps _ (colCfg (p + 1) (a + 1) (b + 1)) =
    some ⟨blank, cons false (app W (app W (rep (p + 1) W (colTail a (b + 1))))), .E⟩
  rw [← e]
  exact h

/-- Collecting, n cycles: the middle block moves into the left block, one word of seven cells for each word of
three. -/
theorem collect_n (n p a b : Nat) :
    ∃ k, steps k (colCfg (p + 1) (a + n) (b + 1)) = some (colCfg (p + 1 + 2 * n) a (b + 1)) := by
  induction n generalizing p with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    have h1 := collect2 p (a + n) b
    obtain ⟨k, hk⟩ := ih (p + 2)
    have e : p + 1 + 2 * (n + 1) = p + 2 + 1 + 2 * n := by omega
    rw [e]
    exact ⟨_, steps_seq trans h1 hk⟩

/-- Right of the left block while expanding, after its first six cells `101100`:
`000 110110011010 10 (110110)^c 000 (110110)^b 110`. -/
def expTail (c b : Nat) : Tape :=
  app [false, false, false, true, true, false, true, true, false, false, true, true, false, true, false, true, false]
    (rep c V (app [false, false, false] (rep b V (app [true, true, false] blank))))

/-- Expanding, at the moment state E reaches the left end: `E> 0 (1011001)^p 1011 0^5 110110011010 (101)^(2c) 1000
(011)^(2b+1)` on an otherwise blank tape. -/
def expCfg (p c b : Nat) : Config :=
  ⟨blank, cons false (rep p W (app [true, false, true, true, false, false] (expTail c b))), .E⟩

/-- One expanding cycle (four visits of the left end): two fewer words in the left block, fourteen more three-cell
words in the middle block. -/
theorem expand4 (p c b : Nat) :
    steps (240 * b + 240 * c + 144 * p + 2812) (expCfg (p + 3) (c + 1) (b + 1)) =
      some (expCfg (p + 1) (c + 8) (b + 1)) := by
  have h := expand_raw b c p
  have e := rep_rotate p [true, false, true, true, false, false] [true, true, false, true, true, false, false] W rfl (expTail (c + 8) (b + 1))
  show steps _ (expCfg (p + 3) (c + 1) (b + 1)) =
    some ⟨blank, cons false (app W (rep p W (app [true, false, true, true, false, false] (expTail (c + 8) (b + 1))))), .E⟩
  rw [← e]
  exact h

/-- Expanding, n cycles: the left block moves into the middle block, seven words of three cells for each word of
seven. -/
theorem expand_n (n p c b : Nat) :
    ∃ k, steps k (expCfg (p + 1 + 2 * n) (c + 1) (b + 1)) = some (expCfg (p + 1) (c + 1 + 7 * n) (b + 1)) := by
  induction n generalizing c with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    have h1 := expand4 (p + 2 * n) c b
    obtain ⟨k, hk⟩ := ih (c + 7)
    have e1 : p + 1 + 2 * (n + 1) = p + 2 * n + 3 := by omega
    have e2 : c + 1 + 7 * (n + 1) = c + 7 + 1 + 7 * n := by omega
    have e3 : p + 2 * n + 1 = p + 1 + 2 * n := by omega
    rw [e1, e2]
    rw [e3] at h1
    exact ⟨_, steps_seq trans h1 hk⟩

end H65826
