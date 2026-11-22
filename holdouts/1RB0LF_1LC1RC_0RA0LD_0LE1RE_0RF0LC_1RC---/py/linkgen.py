"""Write lean/Link.lean: the twin's token rules as runs of this machine, and the round law.

usage: python3 py/linkgen.py > lean/Link.lean

Machine 1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---. The token rules `TV` are those of the twin
1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF (its lean/Tokens.lean). For every rule and every entry form of its kind
this script runs the machine symbolically on the rule's input word (a concrete prefix followed by an unknown token
tape), taking a premise of the rule as one call whenever the head meets that premise's input in one of the
premise's entry forms. It fails loudly if a run gets stuck, reads outside its window, or ends with the wrong tape;
otherwise it prints the run as a Lean proof (concrete stretches by `rfl`, premises by their hypotheses).
"""
import sys

M = "1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---"
TW = {}
for qi, q in enumerate(M.split('_')):
    for c in (0, 1):
        t = q[3 * c:3 * c + 3]
        TW[('ABCDEF'[qi], c)] = None if t[0] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, t[2])

BITS = {'L': [1, 0, 1, 0], 'O': [0, 0, 0], 'I': [1, 0, 0], 'x': [1, 0], 'one': [1], 'z': [0]}
LT = {'L': '.L', 'O': '.O', 'I': '.I', 'x': '.x', 'one': '.one', 'z': '.z'}

# entry forms: name, kind, state, ctx (nearest first), prefix of the input, exit state, exit word after L 0
FORMS = [
    ('FA', 'A', 'B', (1, 0), [], 'E', [0, 0]),
    ('FH1', 'Eh', 'C', (1, 0), [], 'E', [0, 0, 1, 0]),
    ('FH2', 'Eh', 'C', (1, 1), [], 'D', [0, 0, 0, 0]),
    ('FO1', 'E0', 'B', (0, 0), [0], 'E', [0, 0]),
    ('FO2', 'E0', 'C', (1, 0), [0], 'E', [0, 0]),
]
KFORMS = {k: [f for f in FORMS if f[1] == k] for k in ('A', 'Eh', 'E0')}

# the token rules of the twin's Tokens.lean (axEnd is handled by enc [x] = enc [I])
# name, kind, input (tokens, tail), output (tokens, tail), premises [(kind, input, output var)]
RULES = [
    ('aL', 'A', (['L'], 'w'), (['L'], 'b'), [('A', ([], 'w'), 'a'), ('A', ([], 'a'), 'b')]),
    ('aO', 'A', (['O'], 'w'), (['I'], 'w'), []),
    ('aI', 'A', (['I'], 'w'), (['O'], 'a'), [('A', ([], 'w'), 'a')]),
    ('aNil', 'A', ([], 'Z'), (['I'], 'Z'), []),
    ('az', 'A', (['z'], 'w'), (['one'], 'w'), []),
    ('axO', 'A', (['x', 'O'], 'w'), (['O', 'x'], 'w'), []),
    ('axI', 'A', (['x', 'I'], 'w'), (['L', 'O'], 'e'), [('Eh', ([], 'w'), 'e')]),
    ('axL', 'A', (['x', 'L'], 'w'), (['L'], 'b'), [('A', (['x'], 'w'), 'a'), ('A', ([], 'a'), 'b')]),
    ('a1', 'A', (['one'], 'w'), (['O'], 'e'), [('Eh', ([], 'w'), 'e')]),
    ('hL', 'Eh', (['L'], 'w'), (['L'], 'e'), [('Eh', ([], 'w'), 'e')]),
    ('hO', 'Eh', (['O'], 'w'), (['one'], 'w'), []),
    ('hI', 'Eh', (['I'], 'w'), ([], 'e'), [('E0', ([], 'w'), 'e')]),
    ('hNil', 'Eh', ([], 'Z'), (['I'], 'Z'), []),
    ('oO', 'E0', (['O'], 'w'), (['L'], 'w'), []),
    ('oL', 'E0', (['L'], 'w'), (['O'], 'a'), [('A', (['x'], 'w'), 'a')]),
    ('oI', 'E0', (['I'], 'w'), (['O', 'one'], 'w'), []),
    ('oNil', 'E0', ([], 'Z'), (['L'], 'Z'), []),
]

def bits(toks): return [b for t in toks for b in BITS[t]]

class Tape:
    """Cells from position -2 up to m-1 concrete, then the tail (a variable name or 'Z' for blank)."""
    def __init__(s, cells, tail): s.c = list(cells); s.tail = tail
    @property
    def m(s): return len(s.c) - 2
    def get(s, p):
        if p < -2: raise RuntimeError('read left of window')
        while p >= s.m:
            if s.tail != 'Z': raise KeyError(p)
            raise RuntimeError('read past the padding of a blank tail')
        return s.c[p + 2]
    def set(s, p, b): s.get(p); s.c[p + 2] = b

PAD = 14  # zeros put in front of a blank tail

def simulate(name, cells, tail, X, prem, stop):
    """Run from head at 0 (cells start at -2). Returns segments and the final tape."""
    tp = Tape(cells, tail)
    pos, st = 0, X
    segs = []; k = 0; n = 0
    def cfg(): return ([tp.c[p + 2] for p in range(pos - 1, -3, -1)], tp.c[max(pos, -2) + 2:], tp.tail, st, pos)
    while not stop(pos, st, n):
        n += 1
        if n > 10000: raise RuntimeError('loop')
        hit = None
        for i, (pk, pin, pout) in enumerate(prem):
            for f in KFORMS[pk]:
                fname, _, fX, fctx, fpre, fY, fpat = f
                if st != fX or pos - 2 < -2: continue
                if (tp.get(pos - 1), tp.get(pos - 2)) != fctx: continue
                if tp.tail != pin[1] or tp.c[pos + 2:] != fpre + bits(pin[0]): continue
                hit = (i, f); break
            if hit: break
        if hit:
            i, f = hit
            if k: segs.append(('run', k, cfg())); k = 0
            segs.append(('call', i, f[0], cfg()))
            tp.c = tp.c[:pos] + f[6]          # cells -2 .. pos-3 kept, then the exit word from pos-2
            tp.tail = prem[i][2]
            pos -= 3; st = f[5]
            segs.append(('after', cfg()))
            continue
        if pos < -2: raise RuntimeError(f'{name}: left the window')
        try: b = tp.get(pos)
        except KeyError: raise RuntimeError(f'{name}: stuck at the tail in {st}, tape {tp.c} + {tp.tail}')
        t = TW[(st, b)]
        if t is None: raise RuntimeError(f'{name}: halts')
        tp.set(pos, t[0]); pos += t[1]; st = t[2]; k += 1
    if k: segs.append(('run', k, cfg()))
    return segs, tp, st

def same(got, want, z):
    if not z: return got == want
    g = list(got); w = list(want)
    while g and g[-1] == 0: g.pop()
    while w and w[-1] == 0: w.pop()
    return g == w

def bl(bs): return '[' + ', '.join('true' if b else 'false' for b in bs) + ']'
def tailterm(t): return 'blank' if t == 'Z' else f'(E {t})'
def cfgterm(c, lname='L'):
    l, r, tail, st, pos = c
    if pos == -3: return f'⟨tail {lname}, cons ({lname} 0) (app {bl(r)} {tailterm(tail)}), .{st}⟩'
    return f'⟨app {bl(l)} {lname}, app {bl(r)} {tailterm(tail)}, .{st}⟩'
def toks(ts, tail):
    if tail == 'Z': return '[' + ', '.join(LT[t] for t in ts) + ']'
    return ' :: '.join([LT[t] for t in ts] + [tail])
def ptoks(ts, tail):
    s = toks(ts, tail); return s if (tail == 'Z' or not ts) else f'({s})'

def chain(segs, start, prem, lname='L'):
    """Proof term and step count for a list of segments."""
    terms = []; ns = []; cur = start
    for s in segs:
        if s[0] == 'run':
            terms.append(f'(show steps {s[1]} {cur} = some {cfgterm(s[2], lname)} from rfl)')
            ns.append(str(s[1])); cur = cfgterm(s[2], lname)
        elif s[0] == 'call':
            _, i, fn, c = s
            pk = prem[i][0]
            g = f'g{i}' if pk == 'A' else f'g{i}{fn}'
            n = f'n{i}' if pk == 'A' or fn == KFORMS[pk][0][0] else f'm{i}'
            terms.append(f'({g} (app {bl(c[0][2:])} {lname}))'); ns.append(n)
        else:
            cur = cfgterm(s[1], lname)
    body = terms[0]
    for t in terms[1:]: body = f'sq {body} {t}' if body == terms[0] else f'sq ({body}) {t}'
    return body, ' + '.join(ns)

def obtains(prem):
    lines = []
    for i, (pk, pin, pv) in enumerate(prem):
        if pk == 'A': lines.append(f'  obtain ⟨n{i}, g{i}⟩ := h{i}')
        else:
            a, b = [f[0] for f in KFORMS[pk]]
            lines.append(f'  obtain ⟨⟨n{i}, g{i}{a}⟩, ⟨m{i}, g{i}{b}⟩⟩ := h{i}')
    return lines

def rule_proof(rule, form):
    name, kind, inp, out, prem = rule
    fname, _, X, ctx, pre, Y, pat = form
    z = inp[1] == 'Z'
    incells = pre + bits(inp[0]) + ([0] * PAD if z else [])
    segs, tp, st = simulate(f'{name}/{fname}', [ctx[1], ctx[0]] + incells, inp[1], X, prem,
                            lambda pos, st, n: pos < -2)
    want = pat + bits(out[0])
    if st != Y or tp.tail != out[1] or not same(tp.c, want, z):
        raise RuntimeError(f'{name}/{fname}: ends in {st} with {tp.c} + {tp.tail}, want {Y} {want} + {out[1]}')
    hyps = ' '.join(f'(h{i} : Means .{pk} {ptoks(*pin)} {pv})' for i, (pk, pin, pv) in enumerate(prem))
    vs = sorted({v for v in [inp[1], out[1]] + [p[1][1] for p in prem] + [p[2] for p in prem] if v != 'Z'})
    vs = ('{' + ' '.join(vs) + ' : List T} ') if vs else ''
    lines = [f'theorem {name}_{fname} {vs}{hyps} : {fname} {ptoks(*inp)} {ptoks(*out)} := by'] + obtains(prem)
    zt = f'(app (List.replicate {PAD} false) blank)' if z else tailterm(inp[1])
    start = f'⟨app {bl([ctx[0], ctx[1]])} L, app {bl(pre + bits(inp[0]))} {zt}, .{X}⟩'
    body, ns = chain(segs, start, prem)
    if z:
        endr = segs[-1][2][1]
        lines.append(f'  refine ⟨{ns}, fun L => ?_⟩')
        lines.append(f'  have s := {body}')
        lines.append(f'  rw [blank_pad, app_blank_ext {bl(endr)} {bl(want)} (by decide)] at s')
        lines.append(f'  exact s')
    else:
        lines.append(f'  exact ⟨{ns}, fun L => {body}⟩')
    return '\n'.join(lines)

def round_proof():
    prem = [('A', ([], 'S'), 'a')]
    cells = [0, 0] + [0, 0, 0, 1, 0]
    segs, tp, st = simulate('round', cells, 'S', 'E', prem, lambda pos, st, n: n > 0 and pos == -2)
    want = [0, 0, 0, 1, 0, 1, 0]
    if st != 'E' or tp.tail != 'a' or tp.c != want: raise RuntimeError(f'round: {st} {tp.c} {tp.tail}')
    start = f'⟨app [false, false] L, app [false, false, false, true, false] (E S), .E⟩'
    body, ns = chain(segs, start, prem)
    return (f'theorem round_run {{S a : List T}} (h0 : FA S a) :\n'
            f'    ∃ n, 1 ≤ n ∧ ∀ L, steps n ⟨app [false, false] L, app [false, false, false, true, false] (E S), .E⟩ =\n'
            f'      some ⟨L, app [false, false, false, true, false, true, false] (E a), .E⟩ := by\n'
            f'  obtain ⟨n0, g0⟩ := h0\n'
            f'  exact ⟨{ns}, by omega, fun L => {body}⟩')

HEAD = r'''import Machine
import Total
import Need

/-! # The twin's token rules are runs of this machine, and the round law

Machine: 1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---. Its twin 1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF has token
rules `TV` (words `L = 1010`, `O = 000`, `I = 100`, defects `x = 10`, `1`, `0`; the twin's `lean/Tokens.lean`) and
proves in `lean/Total.lean` there that on a tape with at most one defect they always apply (`Z36869.total`). This
file proves, in the kernel, that the same token rules are runs of **this** machine's transition table
(`H83189.trans`), so this machine never halts under exactly the same assumption as the twin (`nonhalt_of_need`).

A token tape `w` is the half tape `E w` to the right of the head. Each kind of token visit is a run from one of
five *entry forms* (state, and the two cells left of the head, nearest first) that ends three cells further left,
having rewritten those two cells, for any tape `L` further left (never read):

* `FA w w'`  (visit of A):  `B` after `1 0` on `E w`  ends in `E` on `L 0 · 0 0 · E w'`.
* `FH1 w w'` (`Eh`, E without its leading `1 0`): `C` after `1 0` on `E w` ends in `E` on `L 0 · 0 0 1 0 · E w'`.
* `FH2 w w'` (`Eh`): `C` after `1 1` on `E w` ends in `D` on `L 0 · 0 0 0 0 · E w'`.
* `FO1 w w'` (`E0`, E after a 0): `B` after `0 0` on `0 · E w` ends in `E` on `L 0 · 0 0 · E w'`.
* `FO2 w w'` (`E0`): `C` after `1 0` on `0 · E w` ends in `E` on `L 0 · 0 0 · E w'`.

* `sound`: every token rule `TV k w w'` holds in all forms of its kind (`Means`). Each of the 25 cases is a few
  stretches of 1 to 17 steps (checked by `rfl`) around calls of the rule's premises; the defect rule `x L` runs the same
  way as on the twin, through the visit of A on `x W` four cells further right. Written by `py/linkgen.py`, which
  finds each run by symbolic simulation.
* `round_run`: in `E` on `0 0 0 1 0 · E S` (anything to the left after two blank cells) the machine reaches `E`
  two cells further left on `0 0 0 1 0 · E (x :: A(S))`, where `FA S A(S)`; from blank tape it is there with
  `S = []` after 4 steps (`start`).
* `round9`: from blank tape this machine is at the start of round 9 (E on `0 0 0 1 0 · x a9`) at step 7,834.
* `nonhalt_of_need`: if every round from round 9 on has `nx W ≤ 1` on its tape `x W` (the twin's hypothesis in
  `F36869.nonhalt_of_need`, word for word, with `nx` and `R9` from the twin's `Need.lean`), this machine never halts
  from blank tape. An earlier version (`nonhalt_of_clean`, PR 416) assumed that every round's defect dies counted from
  round 0; that hypothesis is false (round 2's defect survives, `F36869.old_hyp_false`), so it was removed.
-/

namespace K83189

open TM (cons tail blank app)
open Z36869 (T TV Clean Good)

abbrev steps := H83189.steps

/-- A token tape as the half tape right of the head. -/
def E : List T → TM.Tape
  | [] => blank
  | t :: w => app (Z36869.bits t) (E w)

theorem sq {a b : Nat} {c0 c1 c2 : H83189.Config} (h1 : steps a c0 = some c1) (h2 : steps b c1 = some c2) :
    steps (a + b) c0 = some c2 := TM.steps_seq _ h1 h2

def FA (w w' : List T) : Prop := ∃ n, ∀ L : TM.Tape,
  steps n ⟨app [true, false] L, E w, .B⟩ = some ⟨tail L, cons (L 0) (app [false, false] (E w')), .E⟩
def FH1 (w w' : List T) : Prop := ∃ n, ∀ L : TM.Tape,
  steps n ⟨app [true, false] L, E w, .C⟩ = some ⟨tail L, cons (L 0) (app [false, false, true, false] (E w')), .E⟩
def FH2 (w w' : List T) : Prop := ∃ n, ∀ L : TM.Tape,
  steps n ⟨app [true, true] L, E w, .C⟩ = some ⟨tail L, cons (L 0) (app [false, false, false, false] (E w')), .D⟩
def FO1 (w w' : List T) : Prop := ∃ n, ∀ L : TM.Tape,
  steps n ⟨app [false, false] L, cons false (E w), .B⟩ = some ⟨tail L, cons (L 0) (app [false, false] (E w')), .E⟩
def FO2 (w w' : List T) : Prop := ∃ n, ∀ L : TM.Tape,
  steps n ⟨app [true, false] L, cons false (E w), .C⟩ = some ⟨tail L, cons (L 0) (app [false, false] (E w')), .E⟩

/-- What a token visit means for this machine: a run from each entry form of its kind. -/
def Means : Z36869.TK → List T → List T → Prop
  | .A, w, w' => FA w w'
  | .Eh, w, w' => FH1 w w' ∧ FH2 w w'
  | .E0, w, w' => FO1 w w' ∧ FO2 w w'

/-! ## Blank tails -/

theorem blank_pad : app (List.replicate 14 false) blank = blank := by
  simp only [List.replicate, TM.app_cons, TM.app_nil, TM.cons_false_blank]

theorem app_getD (u : List Bool) : app u blank = fun i => u.getD i false := by
  induction u with
  | nil => rfl
  | cons b u ih => funext i; cases i <;> simp [ih]

theorem getD_of_le (u : List Bool) (i : Nat) (h : u.length ≤ i) : u.getD i false = false := by
  induction u generalizing i with
  | nil => rfl
  | cons b u ih => cases i with
    | zero => simp at h
    | succ i => simp only [List.getD_cons_succ]; exact ih i (by simp at h; omega)

theorem app_blank_ext (u v : List Bool) (h : ∀ i < max u.length v.length, u.getD i false = v.getD i false) :
    app u blank = app v blank := by
  rw [app_getD, app_getD]; funext i
  by_cases hi : i < max u.length v.length
  · exact h i hi
  · rw [getD_of_le u i (by omega), getD_of_le v i (by omega)]

theorem E_x_nil : E [.x] = E [.I] := app_blank_ext [true, false] [true, false, false] (by decide)

/-! ## The token rules as runs (generated by `py/linkgen.py`) -/

'''

FOOT = r'''
/-- Every token rule of the twin is a run of this machine, from every entry form of its kind. -/
theorem sound {k w w'} (h : TV k w w') : Means k w w' := by
  induction h with
  | aL _ _ ih1 ih2 => exact aL_FA ih1 ih2
  | aO w => exact aO_FA
  | aI _ ih => exact aI_FA ih
  | aNil => exact aNil_FA
  | az w => exact az_FA
  | axO w => exact axO_FA
  | axI _ ih => exact axI_FA ih
  | axL _ _ ih1 ih2 => exact axL_FA ih1 ih2
  | a1 _ ih => exact a1_FA ih
  | axEnd _ ih => show FA [.x] _; unfold FA; rw [E_x_nil]; exact ih
  | hL _ ih => exact ⟨hL_FH1 ih, hL_FH2 ih⟩
  | hO w => exact ⟨hO_FH1, hO_FH2⟩
  | hI _ ih => exact ⟨hI_FH1 ih, hI_FH2 ih⟩
  | hNil => exact ⟨hNil_FH1, hNil_FH2⟩
  | oO w => exact ⟨oO_FO1, oO_FO2⟩
  | oL _ ih => exact ⟨oL_FO1 ih, oL_FO2 ih⟩
  | oI w => exact ⟨oI_FO1, oI_FO2⟩
  | oNil => exact ⟨oNil_FO1, oNil_FO2⟩

/-! ## Rounds from blank tape -/

/-- From blank tape, after 4 steps: `E` on `0 0 0 1 0 · E []` with blank tape to the left. -/
theorem start : steps 4 H83189.init = some ⟨blank, app [false, false, false, true, false] (E []), .E⟩ := by
  have h : steps 4 ⟨blank, blank, .A⟩ = some ⟨blank, app [false, false, false, true] blank, .E⟩ := rfl
  rw [show app [false, false, false, true, false] (E []) = app [false, false, false, true] blank from
    app_blank_ext _ _ (by decide)]
  exact h

theorem step_of_good {w} (h : Good w) : ∃ a, TV .A w a := by
  obtain ⟨r, hr, _⟩ := Z36869.total h 1
  obtain ⟨a, ha, h0⟩ := hr.succ_inv
  exact ⟨a, ha⟩

/-! ## From round 9 on

The rounds from blank tape do not all have one defect: round 2's defect survives (`F36869.old_hyp_false` in the
twin's `Fuel.lean`), so a reduction "every round's defect dies, from round 0" would be vacuous. As on the twin, the
reduction starts at round 9, whose tape `x a9` is clean behind the defect, and asks that every round's defect needs
at most one visit (`F36869.nx`, `F36869.R9` from the twin's `Need.lean`). -/

/-- The bits of a word list, head first. -/
def flatK : List T → List Bool
  | [] => []
  | t :: w => Z36869.bits t ++ flatK w

theorem E_flat (w : List T) : E w = app (flatK w) blank := by
  induction w with
  | nil => rfl
  | cons t w ih => show app (Z36869.bits t) (E w) = _; rw [ih, flatK, TM.app_app]

/-- The right half tape at the start of round 9, as the list simulator leaves it (no trailing blanks). -/
def r9 : List Bool := ([false, false, false, true, false] ++ flatK (.x :: F36869.a9)).dropLast.dropLast

theorem r9_eq : [false, false, false, true, false] ++ flatK (.x :: F36869.a9) = r9 ++ [false, false] := by decide

theorem round9_f : H83189.fsteps 7834 (TM.FCfg.blank .A) = some ⟨[], r9, .E⟩ := by decide +kernel

/-- From blank tape this machine reaches the start of round 9, E on `0 0 0 1 0 · x a9` with blank tape to the left,
at step 7,834 (kernel evaluation; the twin gets there at step 5,848). -/
theorem round9 : steps 7834 H83189.init =
    some ⟨blank, app [false, false, false, true, false] (E (.x :: F36869.a9)), .E⟩ := by
  have h := TM.blank_reaches H83189.trans round9_f
  show TM.steps H83189.trans 7834 (TM.blankCfg .A) = _
  rw [h]
  have e1 : app r9 blank = app [false, false, false, true, false] (E (.x :: F36869.a9)) := by
    rw [E_flat, TM.app_app, r9_eq, ← TM.app_app]
    show app r9 blank = app r9 (cons false (cons false blank))
    rw [TM.cons_false_blank, TM.cons_false_blank]
  show some (⟨app [] blank, app r9 blank, .E⟩ : H83189.Config) = _
  rw [e1]; rfl

theorem runs9 (H : ∀ W, F36869.R9 W → F36869.nx W ≤ 1) :
    ∀ k, ∃ W n, F36869.R9 W ∧ k ≤ n ∧
      steps n H83189.init = some ⟨blank, app [false, false, false, true, false] (E (.x :: W)), .E⟩ := by
  intro k
  induction k with
  | zero => exact ⟨F36869.a9, 7834, F36869.R9.base, by omega, round9⟩
  | succ k ih =>
    obtain ⟨W, n, hW, hk, hn⟩ := ih
    have hg : Good (.x :: W) := Or.inr ⟨[], .x, W, Z36869.clean_nil, Or.inl rfl, F36869.r9_clean H hW, rfl⟩
    obtain ⟨a, ha⟩ := step_of_good hg
    obtain ⟨m, hm1, hm⟩ := round_run (sound ha)
    refine ⟨a, n + m, F36869.R9.next hW ha, by omega, ?_⟩
    have h := hm blank
    rw [show app [false, false] blank = blank by simp only [TM.app_cons, TM.app_nil, TM.cons_false_blank]] at h
    exact sq hn h

/-- **The reduction.** If in every round from round 9 on the defect in front needs at most one visit (the twin's
hypothesis in `F36869.nonhalt_of_need`, word for word), this machine never halts from blank tape. -/
theorem nonhalt_of_need (H : ∀ W, F36869.R9 W → F36869.nx W ≤ 1) : ¬ H83189.HaltsFromBlank := by
  apply TM.not_halts_of_forall
  apply TM.forall_of_unbounded _ (fun m => ∃ W, steps m H83189.init =
    some ⟨blank, app [false, false, false, true, false] (E (.x :: W)), .E⟩)
  · intro n
    obtain ⟨W, m, _, hm, h⟩ := runs9 H n
    exact ⟨m, hm, W, h⟩
  · rintro m ⟨W, h⟩
    exact ⟨_, h⟩

end K83189
'''

if __name__ == '__main__':
    out = []
    for rule in RULES:
        for form in KFORMS[rule[1]]:
            out.append(rule_proof(rule, form))
    out.append(round_proof())
    sys.stdout.write(HEAD + '\n\n'.join(out) + '\n' + FOOT)
