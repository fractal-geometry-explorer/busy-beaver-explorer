import Machine

/-!
# One sweep pair is the XOR rule (rule 102), for every word length

Words are 3-cell letters `x = 111` (the bit `false`) and `y = 110` (`true`), listed left to right.  Start in B on the
first cell of a word string `w ++ [y]` (it ends in `y`, so it is a concatenation of runs `1^m 0`), with a 0 after it.

* Right sweep (`rsweep`): B zigzags through each run, `x` becomes `000` and `y` becomes `011`.
* Turn: B on the 0 writes 1 and steps left in C.
* Left sweep (`lsweep`): C means "the word to the right is `y`", E means "it is `x`"; each word is rewritten to the XOR
  of itself and its right neighbour.

`epoch`: the string `w` comes back as `x102 w` (cell `i` is `w[i] xor w[i+1]`, with a `y` after the end), the head in
C or E just left of it, and the 0 after it turned into a 1.  Lucas' theorem for the iterates is in `XorLucas.lean`.
-/

namespace H696

open TM

/-- A word as it lies on the right tape, left to right: `x = 111` (false), `y = 110` (true). -/
def wd : Bool → List Bool
  | false => [true, true, true]
  | true => [true, true, false]

/-- A word string on the right tape, left to right. -/
def enc : List Bool → Tape → Tape
  | [], R => R
  | a :: ws, R => app (wd a) (enc ws R)

/-- What the right sweep leaves for a word, on the left tape nearest first: `000`, or `011` read right to left. -/
def sw : Bool → List Bool
  | false => [false, false, false]
  | true => [true, true, false]

/-- The left tape after the right sweep has passed the words `ws` (left to right). -/
def swL : List Bool → Tape → Tape
  | [], L => L
  | a :: ws, L => swL ws (app (sw a) L)

/-- The parity state of the left sweep: C when the word to the right is `y`, E when it is `x`. -/
def ps : Bool → St
  | true => .C
  | false => .E

/-- The head on the first cell of the tape `X` to its left (the shape a left move produces). -/
def onL (X R : Tape) (q : St) : Config := ⟨tail X, cons (X 0) R, q⟩

theorem eta (X : Tape) : X = cons (X 0) (tail X) := by
  funext n; cases n <;> rfl

theorem enc_append (xs ys : List Bool) (R : Tape) : enc (xs ++ ys) R = enc xs (enc ys R) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.cons_append, enc, ih]

theorem swL_append (xs ys : List Bool) : ∀ L : Tape, swL (xs ++ ys) L = swL ys (swL xs L) := by
  induction xs with
  | nil => intro L; rfl
  | cons a xs ih => intro L; simp only [List.cons_append, swL, ih]

/-! ## The right sweep -/

/-- B zigzags over `x`: three times `B 1 1 → 0 B 1` (the last one looks two cells into the next word, `11`). -/
theorem rx (L R : Tape) :
    steps 9 ⟨L, app [true, true, true] (cons true (cons true R)), .B⟩ =
      some ⟨app [false, false, false] L, cons true (cons true R), .B⟩ := rfl

/-- B over `y`: `B 1 1 0 → 0 1 1 B`. -/
theorem ry (L R : Tape) :
    steps 3 ⟨L, app [true, true, false] R, .B⟩ = some ⟨app [true, true, false] L, R, .B⟩ := rfl

/-- The steps of the right sweep before the last word. -/
def rc : List Bool → Nat
  | [] => 0
  | false :: ws => 9 + rc ws
  | true :: ws => 3 + rc ws

theorem enc_y_head (ws : List Bool) (R : Tape) :
    enc ws (app [true, true, false] R) = cons true (cons true (tail (tail (enc ws (app [true, true, false] R))))) := by
  funext n
  cases ws with
  | nil => rcases n with _ | _ | n <;> rfl
  | cons a ws => cases a <;> rcases n with _ | _ | n <;> rfl

/-- **The right sweep.** -/
theorem rsweep (ws : List Bool) (R : Tape) : ∀ L : Tape,
    steps (rc ws + 3) ⟨L, enc ws (app [true, true, false] R), .B⟩ = some ⟨swL (ws ++ [true]) L, R, .B⟩ := by
  induction ws with
  | nil => intro L; exact ry L R
  | cons a ws ih =>
    intro L
    cases a with
    | false =>
      have h1 : steps 9 ⟨L, enc (false :: ws) (app [true, true, false] R), .B⟩ =
          some ⟨app [false, false, false] L, enc ws (app [true, true, false] R), .B⟩ := by
        show steps 9 ⟨L, app [true, true, true] (enc ws (app [true, true, false] R)), .B⟩ = _
        rw [enc_y_head ws R]
        exact rx L _
      have e : rc (false :: ws) + 3 = 9 + (rc ws + 3) := by simp only [rc]; omega
      rw [e]
      exact steps_seq trans h1 (ih (app [false, false, false] L))
    | true =>
      have h1 : steps 3 ⟨L, enc (true :: ws) (app [true, true, false] R), .B⟩ =
          some ⟨app [true, true, false] L, enc ws (app [true, true, false] R), .B⟩ := ry L _
      have e : rc (true :: ws) + 3 = 3 + (rc ws + 3) := by simp only [rc]; omega
      rw [e]
      exact steps_seq trans h1 (ih (app [true, true, false] L))

/-! ## The left sweep -/

/-- One word of the left sweep: the word becomes its XOR with the word to its right (the state). -/
theorem lsweep1 (a q : Bool) (Y R : Tape) :
    steps 3 (onL (app (sw a) Y) R (ps q)) = some (onL Y (app (wd (bne a q)) R) (ps a)) := by
  rw [eta Y]
  cases a <;> cases q <;> cases h : Y 0 <;> rfl

/-- The first word of a string, or `q` if it is empty. -/
def hd : List Bool → Bool → Bool
  | [], q => q
  | b :: _, _ => b

/-- **Rule 102**: cell `i` becomes `w[i] xor w[i+1]`, with `q` after the end. -/
def x102 : List Bool → Bool → List Bool
  | [], _ => []
  | a :: ws, q => bne a (hd ws q) :: x102 ws q

/-- **The left sweep.** -/
theorem lsweep (ws : List Bool) (q : Bool) (R : Tape) : ∀ S : Tape,
    steps (3 * ws.length) (onL (swL ws S) R (ps q)) = some (onL S (enc (x102 ws q) R) (ps (hd ws q))) := by
  induction ws with
  | nil => intro S; rfl
  | cons a ws ih =>
    intro S
    have h1 := ih (app (sw a) S)
    have h2 := lsweep1 a (hd ws q) S (enc (x102 ws q) R)
    have e : 3 * (a :: ws).length = 3 * ws.length + 3 := by simp [List.length]; omega
    rw [e]
    exact steps_seq trans h1 h2

/-! ## One epoch -/

theorem length_x102 (ws : List Bool) (q : Bool) : (x102 ws q).length = ws.length := by
  induction ws with
  | nil => rfl
  | cons a ws ih => simp [x102, ih]

/-- The last word after an epoch is `x`: `x102 (w ++ [y]) y = x102' ++ [x]`. -/
theorem x102_last (ws : List Bool) : ∃ vs, x102 (ws ++ [true]) true = vs ++ [false] ∧ vs.length = ws.length := by
  induction ws with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons a ws ih =>
    obtain ⟨vs, h, hl⟩ := ih
    refine ⟨bne a (hd (ws ++ [true]) true) :: vs, ?_, by simp [hl]⟩
    show bne a (hd (ws ++ [true]) true) :: x102 (ws ++ [true]) true = _
    rw [h]; rfl

/-- **One epoch is rule 102.**  From B on the first cell of `w ++ [y]` followed by a 0, after a right sweep, a turn and
a left sweep the head is just left of the string in C or E, the string is `x102 (w ++ [y]) y` (whose last word is `x`),
and the 0 after it is now a 1.  Nothing outside the string and that one cell is read. -/
theorem epoch (ws : List Bool) (L R : Tape) :
    steps (rc ws + 3 + 1 + 3 * (ws.length + 1)) ⟨L, enc (ws ++ [true]) (cons false R), .B⟩ =
      some (onL L (enc (x102 (ws ++ [true]) true) (cons true R)) (ps (hd (ws ++ [true]) true))) := by
  have h1 : steps (rc ws + 3) ⟨L, enc (ws ++ [true]) (cons false R), .B⟩ =
      some ⟨swL (ws ++ [true]) L, cons false R, .B⟩ := by
    rw [enc_append]; exact rsweep ws (cons false R) L
  -- B on the 0: write 1, step left in C
  have h2 : steps 1 ⟨swL (ws ++ [true]) L, cons false R, .B⟩ =
      some (onL (swL (ws ++ [true]) L) (cons true R) (ps true)) := rfl
  have h3 := lsweep (ws ++ [true]) true (cons true R) L
  have e : (ws ++ [true]).length = ws.length + 1 := by simp
  rw [e] at h3
  exact steps_seq trans (steps_seq trans h1 h2) h3

/-- Cell by cell: word `i` after the epoch is `w[i] xor w[i+1]` (with `y` after the end). -/
theorem x102_getD (ws : List Bool) (q : Bool) : ∀ i, i < ws.length →
    (x102 ws q).getD i false = bne (ws.getD i false) (ws.getD (i + 1) q) := by
  induction ws with
  | nil => intro i h; simp at h
  | cons a ws ih =>
    intro i h
    cases i with
    | zero => cases ws <;> rfl
    | succ i =>
      have h' : i < ws.length := by simp at h; omega
      show (x102 ws q).getD i false = bne (ws.getD i false) (ws.getD (i + 1) q)
      exact ih i h'

end H696
