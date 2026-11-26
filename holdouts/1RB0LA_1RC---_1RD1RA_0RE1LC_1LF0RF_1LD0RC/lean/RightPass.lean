import Machine

/-! # The left-to-right sweep as a transducer on the words of the left code

When the head leaves the left end, the tape is a word over `X = 0 0 1 1` (a spacer), `Y = 0 0 1 1 1 1 1` (digit 1)
and `Z = 0 0 0 0 0 1 1` (digit 0), plus merged words where a spacer is -1 (checked on the run, not proved; see the
README).  Going right in state C, the head reads one word at a time and leaves the right code behind it
(`x = 0 0 0 1`, `y = 0 0 0 1 1 1 1`, `z = 0 1 1 1 1 1 1`), shifted by one cell.  Between words it is in one of three
scanner states, all in state C, told apart by the 11 cells left of the head:

| scanner state | cells left of the head | after |
|---|---|---|
| `Cx` | `0 0 0 1 0 0 0 1 0 0 0` | a spacer |
| `Cz` | `1 1 1 1 0 0 0 1 0 0 0` | a 0-digit |
| `Cy` | `1 0 0 0 1 1 1 1 0 0 0` | a 1-digit |

`RS.rule` lists the eight crossings, each proved for every tape on both sides (`rule_sound`).  The one left out is
`Cy` on `Z`: a 1-digit right before a 0-digit.  There the head walks back over the block of 1-digits to move it, and
this is where the merged words (spacers of -1) are made.  `pass_sound`: for any word list with no `Y` right before
a `Z`, the machine crosses the whole list, by induction on the list.
-/

namespace H76289

open TM

/-- The words of the left code. -/
inductive Tok where
  | X | Y | Z
  deriving DecidableEq, Repr

/-- The cells of a token, left to right. -/
def Tok.word : Tok → List Bool
  | .X => [false, false, true, true]
  | .Y => [false, false, true, true, true, true, true]
  | .Z => [false, false, false, false, false, true, true]

/-- A token list written in front of the right stream. -/
def encR : List Tok → Tape → Tape
  | [], R => R
  | t :: ts, R => app t.word (encR ts R)

/-- The scanner states of the left-to-right sweep. -/
inductive RS where
  | Cx | Cz | Cy
  deriving DecidableEq, Repr

/-- The machine state of a scanner state. -/
def RS.st : RS → St
  | .Cx => .C
  | .Cz => .C
  | .Cy => .C

/-- The cells just left of the head, nearest first. -/
def RS.ctx : RS → List Bool
  | .Cx => [false, false, false, true, false, false, false, true, false, false, false]
  | .Cz => [false, false, false, true, false, false, false, true, true, true, true]
  | .Cy => [false, false, false, true, true, true, true, false, false, false, true]

/-- Crossing one token: the next scanner state, the cells left behind the context (nearest first), and the number of
steps; `none` where no rule is proved. -/
def RS.rule : RS → Tok → Option (RS × List Bool × Nat)
  | .Cx, .X => some (.Cx, [true, false, false, false], 4)
  | .Cx, .Y => some (.Cy, [false, false, false, true, false, false, false], 33)
  | .Cx, .Z => some (.Cz, [true, true, false, true, false, false, false], 81)
  | .Cz, .X => some (.Cx, [true, true, true, true], 4)
  | .Cz, .Y => some (.Cy, [false, false, false, true, true, true, true], 33)
  | .Cz, .Z => some (.Cz, [true, true, false, true, true, true, true], 81)
  | .Cy, .X => some (.Cz, [false, false, false, true], 4)
  | .Cy, .Y => some (.Cy, [true, true, true, false, false, false, true], 33)
  | _, _ => none

set_option maxRecDepth 20000 in
/-- Each rule is a run of the machine, for every tape on both sides. -/
theorem rule_sound (s : RS) (t : Tok) (s' : RS) (out : List Bool) (n : Nat) (h : s.rule t = some (s', out, n))
    (L R : Tape) :
    steps n ⟨app s.ctx L, app t.word R, s.st⟩ = some ⟨app s'.ctx (app out L), R, s'.st⟩ := by
  cases s <;> cases t <;> simp only [RS.rule, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    (try obtain ⟨rfl, rfl, rfl⟩ := h) <;> first | rfl | (exfalso; exact h)

/-- The pass over a token list: the scanner state at the end, the left stream with everything written, and the
step count; `none` as soon as a token has no rule. -/
def RS.pass : RS → List Tok → Tape → Option (RS × Tape × Nat)
  | s, [], L => some (s, L, 0)
  | s, t :: ts, L =>
    match s.rule t with
    | none => none
    | some (s', out, n) =>
      match RS.pass s' ts (app out L) with
      | none => none
      | some (s'', L', m) => some (s'', L', n + m)

/-- The left-to-right sweep over a whole word list, by induction on the list. -/
theorem pass_sound (ts : List Tok) : ∀ (s : RS) (L R : Tape) (s' : RS) (L' : Tape) (n : Nat),
    s.pass ts L = some (s', L', n) →
    steps n ⟨app s.ctx L, encR ts R, s.st⟩ = some ⟨app s'.ctx L', R, s'.st⟩ := by
  induction ts with
  | nil =>
    intro s L R s' L' n h
    simp only [RS.pass, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  | cons t ts ih =>
    intro s L R s' L' n h
    simp only [RS.pass] at h
    cases hr : s.rule t with
    | none => rw [hr] at h; cases h
    | some r =>
      obtain ⟨s1, out, n1⟩ := r
      rw [hr] at h
      dsimp only at h
      cases hp : RS.pass s1 ts (app out L) with
      | none => rw [hp] at h; cases h
      | some q =>
        obtain ⟨s2, L2, m⟩ := q
        rw [hp] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact steps_seq trans (rule_sound s t s1 out n1 hr L (encR ts R)) (ih s1 (app out L) R _ _ m hp)

end H76289
