import Machine

/-! # The right sweep as a transducer on tokens

At the start of each lap the tape is a word over four tokens: `x = 1 0`, `y = 1 1 0`, `u = 1 0 0`, `v = 1 1 0 0`
(checked on the run, not proved).  Going right, the head reads one token at a time.  Between tokens it is in one of
four scanner states, each a machine state with a fixed word just left of the head:

| scanner state | machine state | cells left of the head |
|---|---|---|
| `D0` | D | `1 0 1 0` |
| `D1` | D | `1 1 1 0` |
| `E`  | E | `1 0 1 0 1` |
| `C`  | C | `1 1 1 0` |

`RS.rule` lists the ten crossings: the scanner state after the token, and the cells the crossing leaves behind the
word (nearest first).  Each is proved for every tape on both sides (`rule_sound`).  The combinations it leaves out are
`D` on `u` and `E` on `v` (which the run never meets), `C` on `y` and `v` (likewise) and `E` on `u`, where the head
turns back into the tape (the start of a left excursion, not covered here).

`pass_sound`: for any token list, as long as `RS.pass` finds a rule for every token, the machine crosses the whole
list, by induction on the list.  The run's own sweeps are this pass up to the first `E`-`u`.
-/

namespace H64598

open TM

/-- The four tokens of the tape at the start of a lap. -/
inductive Tok where
  | x | y | u | v
  deriving DecidableEq, Repr

/-- The cells of a token, left to right. -/
def Tok.word : Tok → List Bool
  | .x => [true, false]
  | .y => [true, true, false]
  | .u => [true, false, false]
  | .v => [true, true, false, false]

/-- A token list written in front of the right stream. -/
def encR : List Tok → Tape → Tape
  | [], R => R
  | t :: ts, R => app t.word (encR ts R)

/-- The scanner states of the right sweep. -/
inductive RS where
  | D0 | D1 | E | C
  deriving DecidableEq, Repr

/-- The machine state of a scanner state. -/
def RS.st : RS → St
  | .D0 => .D
  | .D1 => .D
  | .E => .E
  | .C => .C

/-- The cells just left of the head, nearest first. -/
def RS.ctx : RS → List Bool
  | .D0 => [false, true, false, true]
  | .D1 => [false, true, true, true]
  | .E => [true, false, true, false, true]
  | .C => [false, true, true, true]

/-- Crossing one token: the next scanner state, the cells left behind the context (nearest first), and the number of
steps; `none` where no rule is proved. -/
def RS.rule : RS → Tok → Option (RS × List Bool × Nat)
  | .D0, .x => some (.D1, [false, true], 6)
  | .D0, .y => some (.D0, [true, false, true], 7)
  | .D0, .v => some (.E, [true, false, true], 8)
  | .D1, .x => some (.D1, [true, true], 6)
  | .D1, .y => some (.D0, [true, true, true], 7)
  | .D1, .v => some (.E, [true, true, true], 8)
  | .E, .x => some (.E, [true, true], 26)
  | .E, .y => some (.D1, [false, true, true, true], 31)
  | .C, .x => some (.D0, [true, true], 4)
  | .C, .u => some (.E, [true, true], 5)
  | _, _ => none

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

/-- The right sweep over a whole token list, by induction on the list. -/
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

end H64598
