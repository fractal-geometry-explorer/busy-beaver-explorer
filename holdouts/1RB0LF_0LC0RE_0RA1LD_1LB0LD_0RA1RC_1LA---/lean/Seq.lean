import Machine

/-! # Crossing a list of blocks

A *sequence* is a list of blocks of one form `f t`, each with its own parameter `t`, side by side on one side of the
head.  `sq f ts X` puts them in front of the tape `X` (the first element of the list next to the head), and
`sqr f ts X` puts them in the opposite order (the last element next to the head).

If the head crosses one block `f t` in state `q` and comes out on its far side in the same state `q`, the block
changed to `g t` (with a fixed piece of tape `U` travelling along next to the head), then it crosses any list of
such blocks the same way: that is `seqL` (to the left) and `seqR` (to the right), by induction on the list.  The
order of the list is reversed by a crossing, since the block met first ends up furthest away; `seqL'` and `seqR'`
cross a reversed list.  These are the shift rules of `symtm.py` (`TM.cross_l`, `TM.cross_r`) for blocks that are
not one fixed word but a word with a parameter.  Copied from `bb6-1RB1RF_1LC0LB/lean/Seq.lean` (namespace changed); kernel only. -/

namespace H129771
open TM

/-- The blocks `f t` for `t` in `ts`, in front of `X`, the first next to the head. -/
def sq {α : Type} (f : α → Tape → Tape) : List α → Tape → Tape
  | [], X => X
  | t :: ts, X => f t (sq f ts X)

/-- The blocks `f t` for `t` in `ts`, in front of `X`, the last next to the head. -/
def sqr {α : Type} (f : α → Tape → Tape) (ts : List α) (X : Tape) : Tape :=
  ts.foldl (fun acc t => f t acc) X

theorem sqr_cons {α : Type} (f : α → Tape → Tape) (t : α) (ts : List α) (X : Tape) :
    sqr f (t :: ts) X = sqr f ts (f t X) := rfl

theorem sq_append {α : Type} (f : α → Tape → Tape) (l : List α) (t : α) (X : Tape) :
    sq f (l ++ [t]) X = sq f l (f t X) := by
  induction l with
  | nil => rfl
  | cons s l ih => simp only [List.cons_append, sq, ih]

theorem sqr_eq {α : Type} (f : α → Tape → Tape) (ts : List α) (X : Tape) : sqr f ts X = sq f ts.reverse X := by
  induction ts generalizing X with
  | nil => rfl
  | cons t ts ih => rw [sqr_cons, ih, List.reverse_cons, sq_append]

theorem sq_eq {α : Type} (f : α → Tape → Tape) (ts : List α) (X : Tape) : sq f ts X = sqr f ts.reverse X := by
  rw [sqr_eq, List.reverse_reverse]

/-- Crossing the blocks `ts` to the left. -/
theorem seqL {α : Type} (f g : α → Tape → Tape) (U : Tape → Tape) (q : St)
    (h : ∀ t L R, ∃ n, steps n ⟨f t L, U R, q⟩ = some ⟨L, U (g t R), q⟩) :
    ∀ (ts : List α) (L R : Tape), ∃ n, steps n ⟨sq f ts L, U R, q⟩ = some ⟨L, U (sqr g ts R), q⟩ := by
  intro ts
  induction ts with
  | nil => intro L R; exact ⟨0, rfl⟩
  | cons t ts ih =>
    intro L R
    obtain ⟨n1, h1⟩ := h t (sq f ts L) R
    obtain ⟨n2, h2⟩ := ih L (g t R)
    exact ⟨_, steps_seq trans h1 h2⟩

/-- Crossing the blocks `ts`, written last-first, to the left. -/
theorem seqL' {α : Type} (f g : α → Tape → Tape) (U : Tape → Tape) (q : St)
    (h : ∀ t L R, ∃ n, steps n ⟨f t L, U R, q⟩ = some ⟨L, U (g t R), q⟩) :
    ∀ (ts : List α) (L R : Tape), ∃ n, steps n ⟨sqr f ts L, U R, q⟩ = some ⟨L, U (sq g ts R), q⟩ := by
  intro ts L R
  have h' := seqL f g U q h ts.reverse L R
  rw [sqr_eq g, List.reverse_reverse] at h'
  rw [sqr_eq f]; exact h'

/-- Crossing the blocks `ts` to the right. -/
theorem seqR {α : Type} (f g : α → Tape → Tape) (U : Tape → Tape) (q : St)
    (h : ∀ t L R, ∃ n, steps n ⟨U L, f t R, q⟩ = some ⟨U (g t L), R, q⟩) :
    ∀ (ts : List α) (L R : Tape), ∃ n, steps n ⟨U L, sq f ts R, q⟩ = some ⟨U (sqr g ts L), R, q⟩ := by
  intro ts
  induction ts with
  | nil => intro L R; exact ⟨0, rfl⟩
  | cons t ts ih =>
    intro L R
    obtain ⟨n1, h1⟩ := h t L (sq f ts R)
    obtain ⟨n2, h2⟩ := ih (g t L) R
    exact ⟨_, steps_seq trans h1 h2⟩

/-- Crossing the blocks `ts`, written last-first, to the right. -/
theorem seqR' {α : Type} (f g : α → Tape → Tape) (U : Tape → Tape) (q : St)
    (h : ∀ t L R, ∃ n, steps n ⟨U L, f t R, q⟩ = some ⟨U (g t L), R, q⟩) :
    ∀ (ts : List α) (L R : Tape), ∃ n, steps n ⟨U L, sqr f ts R, q⟩ = some ⟨U (sq g ts L), R, q⟩ := by
  intro ts L R
  have h' := seqR f g U q h ts.reverse L R
  rw [sqr_eq g, List.reverse_reverse] at h'
  rw [sqr_eq f]; exact h'

end H129771
