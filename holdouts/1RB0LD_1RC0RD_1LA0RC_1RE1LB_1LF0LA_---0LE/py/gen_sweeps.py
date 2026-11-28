"""Writes lean/RightPass.lean and lean/LeftPass.lean for 1RB0LD_1RC0RD_1LA0RC_1RE1LB_1LF0LA_---0LE.
usage (from this folder): python3 gen_sweeps.py
RightPass: each token crossing of the right sweep is found by running the machine on the context word and the token,
with every other cell unknown (a crossing that reads an unknown cell is left out); Lean checks each with rfl.
LeftPass: block crossings of the left sweep for every length, proved by bbtools.symtm."""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.symtm import prove, rules_file  # noqa: E402

M = "1RB0LD_1RC0RD_1LA0RC_1RE1LB_1LF0LA_---0LE"
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


toks = {"x": "10", "y": "110", "u": "100", "v": "1100"}
ctxs = {"D0": ("D", "1010"), "D1": ("D", "1110"), "E": ("E", "10101"), "C": ("C", "1110")}
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

ctxs={'D0':('D','1010'),'D1':('D','1110'),'E':('E','10101'),'C':('C','1110')}
toks={'x':'10','y':'110','u':'100','v':'1100'}
def bl(s): return '['+', '.join('true' if c=='1' else 'false' for c in s)+']'
def nf(s): return bl(s[::-1])  # nearest first
L=[]
L.append('''import Machine

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
''')
for t,w in toks.items(): L.append(f"  | .{t} => {bl(w)}\n")
L.append('''
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
''')
open(os.path.join(HERE, '..', 'lean', 'RightPass.lean'), 'w').write(''.join(L))

sp=lambda w:' '.join(w)
L0="D> 0 0 0 0 1"; L1="A> 0 0 0 1 0"; L2="B> 0 1 0 0 0"
R=[
 ("left_L0_1","L 0 (111111)^n 1 1 "+L0+" R","L "+L0+" (011011)^n 0 0 1 R","`L0` crosses a block `1^(6n+2) 0` and stays `L0`."),
 ("left_L0_2","L 0 (111111)^n 1 1 1 1 "+L0+" R","L "+L1+" (110110)^n 1 1 0 0 1 R","`L0` crosses `1^(6n+4) 0` and becomes `L1`."),
 ("left_L0_3","L 0 1 1 (111111)^n 1 1 1 1 "+L0+" R","L "+L2+" (101101)^n 1 0 1 1 0 0 1 R","`L0` crosses `1^(6n+6) 0` and becomes `L2`."),
 ("left_L2_1","L 0 1 1 (111111)^n "+L2+" R","L "+L2+" (101101)^n 1 0 1 R","`L2` crosses `1^(6n+2) 0` and stays `L2`."),
 ("left_L2_2","L 0 (111111)^n 1 1 1 1 "+L2+" R","L "+L0+" (011011)^n 0 1 1 0 1 R","`L2` crosses `1^(6n+4) 0` and becomes `L0`."),
 ("left_L2_3","L 0 (111111)^n 1 1 1 1 1 1 "+L2+" R","L "+L1+" (110110)^n 1 1 0 1 1 0 1 R","`L2` crosses `1^(6n+6) 0` and becomes `L1`."),
]
thms=[]
for name,a,b,doc in R:
    try:
        txt,fin=prove(M,name,a,b,doc=doc); thms.append(txt); print('OK',name,fin,file=sys.stderr)
    except Exception as e: print('ERR',name,e,file=sys.stderr)
open(os.path.join(HERE, '..', 'lean', 'LeftPass.lean'), 'w').write(rules_file("Machine","H64598",thms,"""# The left sweep over the blocks `1^(2k) 0`

Going right, the head leaves behind blocks `1^(2k) 0` (`RightPass.lean`); going left it reads them back, one block
at a time, and writes tokens again.  Between blocks it stands on the `0` that ends a block, in one of three states,
each a machine state with a fixed word right of the head: `L0` (D, `0 0 0 1`), `L1` (A, `0 0 1 0`), `L2` (B,
`1 0 0 0`).  From `L0` and `L2` the next state depends only on k mod 3: one more `1^6` adds 30 steps and writes one
more period (`TM.cross_l`).  From `L0`, k = 1, 2, 3 (mod 3) give `L0`, `L1`, `L2`; from `L2` they give `L2`, `L0`,
`L1`.  `L1` first makes a short trip right over the tokens it has just written (11 cells), so its crossing depends on
them and is not stated here.  Generated by `py/gen_sweeps.py` with `bbtools.symtm`; every theorem is for every n and every
tape on both sides."""))
