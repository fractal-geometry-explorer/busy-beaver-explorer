"""Writes lean/RightPass.lean for 1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC.
usage (from this folder): python3 py/gen_rightpass.py
Each token crossing of the left-to-right sweep is found by running the machine on the context word and the token,
with every other cell unknown (a crossing that reads an unknown cell is left out); Lean checks each with rfl."""
import os

HERE = os.path.dirname(os.path.abspath(__file__))
M = "1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC"
T = {}
for s, g in enumerate(M.split("_")):
    for b in (0, 1):
        x = g[3 * b:3 * b + 3]
        T[("ABCDEF"[s], b)] = None if x[0] == "-" else (int(x[0]), 1 if x[1] == "R" else -1, x[2])


def run_right(state, ctx, tok, maxs=2000):
    """ctx tok, head on the first cell of tok, other cells unknown; run until the head first stands right of tok."""
    tape = {i - len(ctx): int(c) for i, c in enumerate(ctx)}
    tape.update({i: int(c) for i, c in enumerate(tok)})
    p, s = 0, state
    for n in range(1, maxs + 1):
        if p not in tape:
            return None
        t = T[(s, tape[p])]
        if t is None:
            return None
        tape[p] = t[0]
        p += t[1]
        s = t[2]
        if p == len(tok):
            return n, s, "".join(str(tape[i]) for i in range(-len(ctx), len(tok)))
    return None


toks = {"X": "0011", "Y": "0011111", "Z": "0000011"}
ctxs = {"Cx": ("C", "00010001000"), "Cz": ("C", "11110001000"), "Cy": ("C", "10001111000")}
rules = []
for name, (st, ctx) in ctxs.items():
    for t, w in toks.items():
        r = run_right(st, ctx, w)
        if r is None:
            continue
        n, s2, left = r
        tgt = next((n2 for n2, (st2, c2) in ctxs.items() if st2 == s2 and left.endswith(c2)), None)
        if tgt is None:
            continue
        rules.append((name, t, tgt, left[:len(left) - len(ctxs[tgt][1])], n))

def bl(s): return '['+', '.join('true' if c=='1' else 'false' for c in s)+']'
def nf(s): return bl(s[::-1])  # nearest first
L=[]
L.append('''import Machine

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
''')
for t,w in toks.items(): L.append(f"  | .{t} => {bl(w)}\n")
L.append('''
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
''')
for n,(st,c) in ctxs.items(): L.append(f"  | .{n} => {nf(c)}\n")
L.append('''
/-- Crossing one token: the next scanner state, the cells left behind the context (nearest first), and the number of
steps; `none` where no rule is proved. -/
def RS.rule : RS → Tok → Option (RS × List Bool × Nat)
''')
have=set()
for (a,t,b,out,n) in rules:
    L.append(f"  | .{a}, .{t} => some (.{b}, {nf(out)}, {n})\n"); have.add((a,t))
L.append("  | _, _ => none\n")
L.append('''
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
''')
open(os.path.join(HERE, '..', 'lean', 'RightPass.lean'), 'w').write(''.join(L))
for r in rules: print(r)
