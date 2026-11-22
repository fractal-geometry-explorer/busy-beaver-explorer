import Sweep

/-!
# The round trip on the list of 4k+3 blocks is a prefix XOR

Away from the two ends of the tape, a round trip of 1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB--- is a map on words over
two 4-cell letters, `s = 0111` (a block starts) and `c = 1111` (a block goes on).  A block of 4k+3 ones and the 0
before it is `s c^k`.

* Leftward sweep (`left_sweep`): each block `s c^k` becomes the group `G_k = 1 (0101)^k 000`, one cell further right.
* Rightward sweep (`right_sweep`): the head alternates between E and A from group to group.  A group read in E
  becomes `s^(k+1)`; a group read in A becomes `c^(k+1)` and also turns the `s` just behind it into `c`
  (`group_A`, `group_E` in `Sweep.lean`).  As a letter word, the output is the prefix XOR (`pxor`) of the input word:
  the bit `s`/`c` written at each letter is the parity of the number of block starts read so far.

So, as letter words with `s = true`, one round trip sends `z` to `pxor false z`, and the word before a round trip is
the XOR of neighbouring letters of the word after it: run backwards, the round trip is the XOR cellular automaton
(elementary rule 102).  The two ends of the tape are not covered here.

Everything in this file is proved from the machine table by the kernel (no `native_decide`).
-/

namespace H76942

open TM

/-- The letter `s = 0111`, as a left tape word (nearest cell first). -/
def sL : List Bool := [true, true, true, false]
/-- The letter `c = 1111`. -/
def cL : List Bool := [true, true, true, true]

/-- The group `G_n = 1 (0101)^n 0 0 0` in front of the right tape `R`. -/
def G (n : Nat) (R : Tape) : Tape :=
  cons true (rep n [false, true, false, true] (cons false (cons false (cons false R))))

/-! ## Rightward sweep -/

/-- Groups in pairs (the first read in E, the second in A), left to right. -/
def grs : List (Nat × Nat) → Tape → Tape
  | [], R => R
  | (a, b) :: ps, R => G a (G b (grs ps R))

/-- The left tape the rightward sweep leaves behind `X`. -/
def outL : List (Nat × Nat) → Tape → Tape
  | [], X => X
  | (a, b) :: ps, X => outL ps (rep (b + 1) cL (rep a sL (app sL X)))

/-- Steps of the rightward sweep. -/
def cost : List (Nat × Nat) → Nat
  | [] => 0
  | (a, b) :: ps => (4 * a + 4) + (28 * b + 30) + cost ps

theorem two_ones_rep (b : Nat) (X : Tape) :
    cons true (cons true (rep b cL (cons true (cons true X)))) = rep (b + 1) cL X := by
  have h := rep_rotate b [true, true] cL cL rfl (cons true (cons true X))
  simp only [app_cons, app_nil] at h
  rw [h]
  exact rep_app_comm b cL X

/-- One pair of groups: `X s E> G_a G_b R` to `X s s^a c^(b+1) s E> R`. -/
theorem pair (a b : Nat) (X R : Tape) :
    steps ((4 * a + 4) + (28 * b + 30)) ⟨app sL X, G a (G b R), .E⟩ =
      some ⟨app sL (rep (b + 1) cL (rep a sL (app sL X))), R, .E⟩ := by
  have h1 := group_E a (app sL X) (G b R)
  have h2 := group_A b (rep a sL (app sL X)) R
  have h1' : steps (4 * a + 4) ⟨app sL X, G a (G b R), .E⟩ =
      some ⟨cons true (cons true (cons true (cons false (rep a sL (app sL X))))), G b R, .A⟩ := h1
  have h2' : steps (28 * b + 30) ⟨cons true (cons true (cons true (cons false (rep a sL (app sL X))))), G b R, .A⟩ =
      some ⟨app sL (rep (b + 1) cL (rep a sL (app sL X))), R, .E⟩ := by
    rw [← two_ones_rep]; exact h2
  exact steps_seq trans h1' h2'

/-- The rightward sweep over any list of pairs of groups. -/
theorem right_sweep (ps : List (Nat × Nat)) :
    ∀ X R : Tape, steps (cost ps) ⟨app sL X, grs ps R, .E⟩ = some ⟨app sL (outL ps X), R, .E⟩ := by
  induction ps with
  | nil => intro X R; rfl
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    intro X R
    exact steps_seq trans (pair a b X (grs ps R)) (ih _ R)

/-! ## The rightward sweep as a prefix XOR of letter words -/

/-- Prefix XOR: the `i`-th output is the XOR of `c` and the first `i + 1` inputs. -/
def pxor : Bool → List Bool → List Bool
  | _, [] => []
  | c, x :: xs => (c ^^ x) :: pxor (c ^^ x) xs

/-- XOR of neighbours, with `c` before the first letter: the inverse of `pxor c`. -/
def xdiff : Bool → List Bool → List Bool
  | _, [] => []
  | c, x :: xs => (c ^^ x) :: xdiff x xs

theorem xdiff_pxor (c : Bool) (w : List Bool) : xdiff c (pxor c w) = w := by
  induction w generalizing c with
  | nil => rfl
  | cons x xs ih =>
    simp only [pxor, xdiff, ih]
    cases c <;> cases x <;> rfl

theorem pxor_xdiff (c : Bool) (w : List Bool) : pxor c (xdiff c w) = w := by
  induction w generalizing c with
  | nil => rfl
  | cons x xs ih =>
    simp only [pxor, xdiff]
    have : (c ^^ (c ^^ x)) = x := by cases c <;> cases x <;> rfl
    rw [this, ih]

theorem pxor_append (c : Bool) (u v : List Bool) :
    pxor c (u ++ v) = pxor c u ++ pxor ((u.foldl (· ^^ ·) c)) v := by
  induction u generalizing c with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, pxor, ih, List.foldl]

/-- Letter words (`true` = `s`, `false` = `c`, left to right) written onto a left tape. -/
def lets : List Bool → Tape → Tape
  | [], X => X
  | z :: zs, X => lets zs (app (if z then sL else cL) X)

theorem lets_append (u v : List Bool) (X : Tape) : lets (u ++ v) X = lets v (lets u X) := by
  induction u generalizing X with
  | nil => rfl
  | cons z zs ih => exact ih _

theorem lets_replicate (n : Nat) (z : Bool) (X : Tape) :
    lets (List.replicate n z) X = rep n (if z then sL else cL) X := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, lets, ih, rep_app_comm]

/-- The letter word of a list of pairs of groups: group `G_k` is the block `s c^k` it came from. -/
def inWord : List (Nat × Nat) → List Bool
  | [] => []
  | (a, b) :: ps => (true :: List.replicate a false) ++ (true :: List.replicate b false) ++ inWord ps

theorem pxor_replicate_false (c : Bool) (n : Nat) : pxor c (List.replicate n false) = List.replicate n c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, pxor, Bool.xor_false, ih, List.replicate_succ]

theorem foldl_replicate_false (c : Bool) (n : Nat) : (List.replicate n false).foldl (· ^^ ·) c = c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.foldl, Bool.xor_false, ih]

/-- The prefix XOR of one pair: `1 0^a 1 0^b` goes to `1^(a+1) 0^(b+1)`, and the parity is back to `false`. -/
theorem pxor_pair (a b : Nat) (w : List Bool) :
    pxor false ((true :: List.replicate a false) ++ (true :: List.replicate b false) ++ w) =
      List.replicate (a + 1) true ++ List.replicate (b + 1) false ++ pxor false w := by
  rw [List.append_assoc, pxor_append, pxor_append]
  simp only [pxor, List.foldl, Bool.not_true, Bool.not_false,
    pxor_replicate_false, foldl_replicate_false, Bool.xor_true]
  simp [List.replicate_succ, List.append_assoc]

/-- **The rightward sweep is a prefix XOR.**  What it leaves behind `X` is the prefix XOR of the letter word of the
groups it read. -/
theorem outL_eq_pxor (ps : List (Nat × Nat)) : ∀ X : Tape, outL ps X = lets (pxor false (inWord ps)) X := by
  induction ps with
  | nil => intro X; rfl
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    intro X
    rw [outL, ih, inWord, pxor_pair, lets_append, lets_append, lets_replicate, lets_replicate, rep_app_comm]
    rfl

/-- The same, read backwards: the letter word before the sweep is the XOR of neighbouring letters after it. -/
theorem inWord_eq_xdiff (ps : List (Nat × Nat)) : inWord ps = xdiff false (pxor false (inWord ps)) :=
  (xdiff_pxor false _).symm

/-! ## Leftward sweep -/

/-- Blocks on a left tape, nearest block first: `blocks [k₁, k₂, …] X` is `X … s c^k₂ s c^k₁`. -/
def blocks : List Nat → Tape → Tape
  | [], X => X
  | k :: ks, X => rep k cL (app sL (blocks ks X))

/-- Groups on a right tape, in the order the leftward sweep makes them (nearest block last). -/
def gs : List Nat → Tape → Tape
  | [], R => R
  | k :: ks, R => gs ks (G k R)

/-- Steps of the leftward sweep. -/
def lcost : List Nat → Nat
  | [] => 0
  | k :: ks => (8 * k + 6) + lcost ks

theorem block_G (k : Nat) (R : Tape) :
    cons false (cons false (cons true (cons false (rep k [true, false, true, false] (cons false (cons false R)))))) =
      cons false (cons false (G k R)) := by
  have h := rep_rotate k [false] [true, false, true, false] [false, true, false, true] rfl (cons false (cons false R))
  simp only [app_cons, app_nil] at h
  show cons false (cons false (cons true (cons false (rep k [true, false, true, false] (cons false (cons false R)))))) =
    cons false (cons false (cons true (rep k [false, true, false, true] (cons false (cons false (cons false R))))))
  rw [h]

/-- The leftward sweep over any list of blocks: `X s c^kₙ … s c^k₁ B> 0 0 0 R` to `X B> 0 0 0 G_kₙ … G_k₁ R`. -/
theorem left_sweep (ks : List Nat) :
    ∀ X R : Tape, steps (lcost ks) ⟨blocks ks X, cons false (cons false (cons false R)), .B⟩ =
      some ⟨X, cons false (cons false (cons false (gs ks R))), .B⟩ := by
  induction ks with
  | nil => intro X R; rfl
  | cons k ks ih =>
    intro X R
    have h1 := block_B k (blocks ks X) (cons false (cons false R))
    rw [block_G] at h1
    have h1' : steps (8 * k + 6) ⟨blocks (k :: ks) X, cons false (cons false (cons false R)), .B⟩ =
        some ⟨blocks ks X, cons false (cons false (cons false (G k R))), .B⟩ := h1
    exact steps_seq trans h1' (ih X (G k R))

end H76942
