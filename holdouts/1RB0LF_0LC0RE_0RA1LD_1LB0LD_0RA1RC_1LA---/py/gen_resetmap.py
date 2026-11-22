"""Writes lean/ResetMapRuns.lean: the runs of the head part of a phase, for the reset map X' = floor(3X/2) + 1 / + 3.

The tape at a reset is  0^inf 1 B> 1 0 (10)^X T.  Everything the run does left of the tail T follows from X alone;
the tail is entered only by *excursions*: the head reads the first cell of the tail (in a state q, with the cells u
on its left), stays in the tail and the u cells, and leaves them to the left (in a state q', having written the
cells v where u was).  Lean's `Exc u q q' v T T'` says that, for every tape on the left.

A *piece* is a run of the head part from one configuration to another, cut at its excursions.  For each piece this
script runs the head part symbolically (bbtools.symtm, the tail an unknown context) and, at each excursion, asks a
direct simulation of the real run what the excursion does (state and cells when it leaves).  It does this for
several resets of both machines and checks that the excursion signatures (u, q, q', v) agree; the symbolic segments
between excursions are then proved in Lean by `symtm.prove` (valid for every value of the parameters and every
tail), and the signatures become the hypotheses of the composition theorems in lean/ResetMap.lean.

The pieces:
  re   reset with X = 2x + 36 (even)        -> the phase record S (x + 5) 1
  ro   reset with X = 2x + 37 (odd)         -> the phase record S (x + 6) 1
  g    the phase record S (a + 2) b          -> S a (b + 3)              (two increments, one excursion)
  e0   S 0 b                                 -> reset with X = 2b + 20
  e1   S 1 b                                 -> reset with X = 2b + 23
where S a b is the record  0^inf B> 0 (10)^(2a+9) 0 0 (10)^(2b+11) 1 T.

usage: python3 gen_resetmap.py      (about a minute)
"""
import re
import os
import sys

here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(here, '../../../tools/py'))
from bbtools import symtm
from bbtools.symtm import Ctx, Rep, Blank, lin, canon
from bbtools.machine import Machine

MS = '1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---'
MACH = Machine.parse(MS)
ST = 'ABCDEF'
MLEN = 4

# ------------------------------------------------------------------ direct simulation
W = {'A': (1, 0), 'B': (0, 0), 'C': (0, 1), 'D': (1, 0), 'E': (0, 1), 'F': (1, None)}
MV = {'A': (1, -1), 'B': (-1, 1), 'C': (1, -1), 'D': (-1, -1), 'E': (1, 1), 'F': (-1, 0)}
NX = {'A': ('B', 'F'), 'B': ('C', 'E'), 'C': ('A', 'D'), 'D': ('B', 'D'), 'E': ('A', 'C'), 'F': ('A', None)}


class Conc:
    def __init__(self, start):
        self.t, self.h, self.s, self.st, self.lo = {}, 0, start, 0, 0

    def is_record(self):
        return self.s == 'B' and self.h < self.lo

    def step(self):
        c = self.t.get(self.h, 0)
        if self.s == 'F' and c == 1:
            raise RuntimeError('the direct run halts')
        if self.is_record():
            self.lo = self.h
        self.t[self.h] = W[self.s][c]
        self.h += MV[self.s][c]
        self.s = NX[self.s][c]
        self.st += 1

    def cells(self, a, b):
        return [self.t.get(k, 0) for k in range(a, b)]

    def blocks(self, k, maxblocks):
        """P-blocks from cell k on: [(D, x)]."""
        out, n = [], 0
        while len(out) < maxblocks:
            if self.t.get(k, 0) == 1 and self.t.get(k + 1, 0) == 0:
                n, k = n + 1, k + 2
                continue
            out.append((n, self.t.get(k, 0)))
            n, k = 0, k + 1
        return out


def resets(start, maxsteps):
    """(step, X) of the resets  1 B> 1 0 (10)^X  of a direct run."""
    c, out = Conc(start), []
    while c.st < maxsteps:
        if c.is_record() and c.t.get(c.h, 0) == 1 and c.t.get(c.h - 1, 0) == 1 and c.t.get(c.h + 1, 0) == 0:
            X = c.blocks(c.h + 2, 1)[0][0]
            if X > 5:
                out.append((c.st, X))
        c.step()
    return out


def goto(start, pred):
    c = Conc(start)
    while not (c.is_record() and pred(c)):
        c.step()
    return c


# ------------------------------------------------------------------ symbolic side
def is_rec(c):
    return c.state == 1 and len(c.left) == 1 and not c.steps.is_zero()


def is_reset(c):
    return (c.state == 1 and c.left == [Blank(), 1] and not c.steps.is_zero() and len(c.right) > 1
            and c.right[0] == 1 and c.right[1] == 0)


def touches(c):
    return isinstance(c.right[0], Ctx)


def unroll(left):
    r = left[-1]
    if not r.n.surely_ge(1):
        raise RuntimeError('cannot unroll %s' % (r,))
    rest = [Rep(r.word, r.n - 1)] if not (r.n - 1).is_zero() else []
    return left[:-1] + rest + list(r.word)


def pop_cells(left, k):
    """The last k cells of a left token list (left to right) and the rest."""
    left, out = list(left), []
    while len(out) < k:
        while not isinstance(left[-1], int):
            left = unroll(left)
        out.append(left.pop())
    return out[::-1], left


def toklen(tks, env):
    n = 0
    for t in tks:
        n += 1 if isinstance(t, int) else len(t.word) * t.n.subs(env)
    return n


def expand(tks, env):
    out = []
    for t in tks:
        out += [t] if isinstance(t, int) else list(t.word) * t.n.subs(env)
    return out


def hybrid(conc, start, env, stop, maxexc=40):
    """Run the symbolic configuration `start` (tail a context) next to the direct run `conc`, which must be at the
    same configuration.  Returns (segments, excursions): segments are (start, end) symbolic configurations,
    excursions (u, q, q2, v) with u, v left to right."""
    c = symtm.Config.parse(start)
    i = [k for k, x in enumerate(c.right) if isinstance(x, Ctx)][0]
    b = conc.h + toklen(c.right[:i], env)
    assert expand(c.right[:i], env) == conc.cells(conc.h, b), 'start does not match the direct run'
    assert expand(c.left[1:], env) == conc.cells(conc.h - toklen(c.left[1:], env), conc.h)
    segs, excs, seg0, k = [], [], c.copy(), 0
    while True:
        c.steps = lin(0)
        symtm.run(MACH, c, lambda x: stop(x) or touches(x), max_moves=100000, rotate=True)
        for _ in range(c.steps.subs(env)):
            conc.step()
        segs.append((seg0, c.copy()))
        if not touches(c):
            assert conc.s == ST[c.state] and expand(c.right[:-1], env)[:50] == conc.cells(conc.h, conc.h + 50)[:len(expand(c.right[:-1], env)[:50])]
            return segs, excs
        assert conc.h == b and conc.s == ST[c.state], 'entry does not match'
        u, rest = pop_cells(c.left, MLEN)
        assert u == conc.cells(b - MLEN, b)
        q = ST[c.state]
        while conc.h >= b - MLEN:
            conc.step()
        v, q2 = conc.cells(b - MLEN, b), conc.s
        excs.append((tuple(u), q, q2, tuple(v)))
        k += 1
        if k > maxexc:
            raise RuntimeError('too many excursions')
        (last,), rest = pop_cells(rest, 1)
        c = symtm.Config(rest, ST.index(q2), [last] + list(v) + [Ctx('T%d' % k)])
        seg0 = c.copy()


def count_stop(pred, n):
    cnt = [0]

    def stop(c):
        if pred(c):
            cnt[0] += 1
            return cnt[0] >= n
        return False
    return stop


# ------------------------------------------------------------------ the pieces
L12 = '0 1 0 1 0 1 0 1 0 1 0 0'
L20 = ' '.join(['0 1'] * 10)


def S(a, b, T='T'):
    """0^inf B> 0 (10)^(2a+9) 0 0 (10)^(2b+11) 1 T  as the run writes it."""
    return '0^inf B> (0101)^%s %s (0101)^%s %s %s' % (a, L12, b, L20, T)


PIECES = {
    're': dict(start='0^inf 1 B> 1 0 (1010)^x+18 T', param='x', nrec=11, pred=is_rec,
               inst=lambda X: X % 2 == 0, env=lambda X: {'x': (X - 36) // 2}),
    'ro': dict(start='0^inf 1 B> 1 0 10 (1010)^x+18 T', param='x', nrec=10, pred=is_rec,
               inst=lambda X: X % 2 == 1, env=lambda X: {'x': (X - 37) // 2}),
    'e0': dict(start=S(0, 'b+1'), param='b', nrec=1, pred=is_reset, D=5),
    'e1': dict(start=S(1, 'b+1'), param='b', nrec=1, pred=is_reset, D=7),
}


def instances_reset(start, cond, n, maxsteps):
    return [(s, X) for s, X in resets(start, maxsteps) if cond(X) and X >= 40][:n]


def run_piece(name, verbose=True):
    """Hybrid runs of a piece on several real instances; the signatures must agree."""
    p = PIECES[name]
    results = []
    for start in 'AD':
        if name in ('re', 'ro'):
            for s, X in instances_reset(start, p['inst'], 3, 3e6):
                conc = goto(start, lambda c, s=s: c.st == s)
                env = p['env'](X)
                segs, excs = hybrid(conc, p['start'], env, count_stop(p['pred'], p['nrec']))
                results.append(((start, X), segs, excs))
        else:
            # phase records S e b: 'o o' records with D = 9 or 11, Y odd >= 13
            seen = 0
            conc = Conc(start)
            while seen < 3 and conc.st < 3e6:
                if conc.is_record() and conc.t.get(conc.h, 0) == 0:
                    bl = conc.blocks(conc.h + 1, 3)
                    if bl[0] == (p['D'], 0) and bl[1] == (0, 0) and bl[2][1] == 1 and bl[2][0] >= 11 and bl[2][0] % 2:
                        Y = bl[2][0]
                        env = {'b': (Y - 11) // 2}
                        c2 = Conc(start)
                        while c2.st < conc.st:
                            c2.step()
                        segs, excs = hybrid(c2, p['start'], env, count_stop(p['pred'], p['nrec']))
                        results.append(((start, 'Y=%d' % Y), segs, excs))
                        seen += 1
                conc.step()
    sigs = set(tuple(r[2]) for r in results)
    if verbose:
        for inst, segs, excs in results:
            print(name, inst, ' '.join('%s%s>%s%s' % (''.join(map(str, u)), q, q2, ''.join(map(str, v)))
                                       for u, q, q2, v in excs), file=sys.stderr)
    assert len(sigs) == 1, 'excursion signatures differ between instances'
    return results[0][1], results[0][2]


def generic_piece():
    """S (a+2) b -> S a (b+3): symbolic only (the signature is the one of every phase step, see README)."""
    st = S('d+2', 'b+1')
    c = symtm.Config.parse(st)
    symtm.run(MACH, c, touches, max_moves=100000, rotate=True)
    u, rest = pop_cells(c.left, MLEN)
    segs = [(symtm.Config.parse(st), c.copy())]
    (last,), rest = pop_cells(rest, 1)
    e = symtm.Config(rest, ST.index('D'), [last, 0, 0, 1, 0, Ctx('T1')])
    e2 = e.copy()
    e2.steps = lin(0)
    symtm.run(MACH, e2, count_stop(is_rec, 3), max_moves=100000, rotate=True)
    segs.append((e, e2))
    return segs, [(tuple(u), ST[c.state], 'D', (0, 0, 1, 0))]


def check_generic_signature(nrec=4000):
    """Every phase step of both direct runs (first nrec records) with a record S a b (a, b >= 0) has the
    generic signature."""
    bad = good = 0
    for start in 'AD':
        conc = Conc(start)
        rec = 0
        while rec < nrec:
            if conc.is_record():
                rec += 1
                if conc.t.get(conc.h, 0) == 0:
                    bl = conc.blocks(conc.h + 1, 3)
                    if (bl[0][1] == 0 and bl[0][0] >= 9 and bl[0][0] % 2 and bl[1] == (0, 0) and bl[2][1] == 1
                            and bl[2][0] >= 11 and bl[2][0] % 2):
                        D, Y = bl[0][0], bl[2][0]
                        env = {'d': (D - 9) // 2, 'b': (Y - 11) // 2}
                        c2 = Conc(start)
                        c2.t, c2.h, c2.s, c2.st, c2.lo = dict(conc.t), conc.h, conc.s, conc.st, conc.lo
                        segs, excs = hybrid(c2, S('d+2', 'b+1'), env, count_stop(is_rec, 3))
                        if [tuple(e) for e in excs] == [((1, 1, 0, 0), 'A', 'D', (0, 0, 1, 0))]:
                            good += 1
                        else:
                            bad += 1
            conc.step()
    print('generic phase steps: %d with the signature, %d without' % (good, bad), file=sys.stderr)
    assert bad == 0
    return good


# ------------------------------------------------------------------ Lean output
def lean_list(bits):
    return '[' + ', '.join('true' if x else 'false' for x in bits) + ']'


CROSS_R0 = """
/-- `cross_r` with nothing between the head and the crossed block.  Stating that case through `app [] L` makes
the kernel unfold the repeat count (x + 18 levels of `rep` and `steps`) when it compares with `L`; going through
this lemma, proved once for every count, avoids that. -/
theorem cross_r0 {s : Nat} {q : St} {w v : List Bool}
    (h : ∀ L R : Tape, steps s ⟨L, app w R, q⟩ = some ⟨app v L, R, q⟩) (k : Nat) :
    ∀ L R : Tape, steps (k * s) ⟨L, rep k w R, q⟩ = some ⟨rep k v L, R, q⟩ := by
  have := cross_r (u := []) (δ := trans) (fun L R => by simpa only [app_nil] using h L R) k
  intro L R; simpa only [app_nil] using this L R
"""


def kernel_friendly(txt):
    """Crossings with an empty word u next to the head go through `cross_r0` (above) instead of `cross_r`."""
    lines = txt.split('\n')
    out, empty = [], set()
    for ln in lines:
        st = ln.strip()
        if st.startswith('have c') and 'app [] ' in st:
            m = re.fullmatch(r'(\s*have (c\d+) : ∀ L R : Tape, steps \d+ ⟨)app \[\] L(, app \[[a-z, ]*\] R, \.[A-F]⟩ = '
                             r'some ⟨)app \[\] \((app \[[a-z, ]*\] L)\)(, R, \.[A-F]⟩ := fun _ _ => rfl)', ln)
            assert m, ln
            empty.add(m.group(2))
            ln = m.group(1) + 'L' + m.group(3) + m.group(4) + m.group(5)
        elif st.startswith('cross_l trans c'):
            assert st.split()[2] not in empty
        elif st.startswith('cross_r trans c') and st.split()[2] in empty:
            ln = ln.replace('cross_r trans c', 'cross_r0 c', 1)
        out.append(ln)
    return '\n'.join(out)


def emit_piece(name, segs, excs, lines):
    """Theorems name_s0 ... (segments), and the data the composition needs."""
    info = []
    for i, (a, b) in enumerate(segs):
        a = a.copy()
        a.steps = lin(0)
        txt, fin = symtm.prove(MS, '%s_s%d' % (name, i), a, b, rotate=True, count_first=True, max_seg=16)
        lines.append(kernel_friendly(txt))
        info.append((a, fin))
    return info


# The pieces as theorems: (name, params, start (Lean), end (Lean), prefix length of the end's tail (cells, as a
# function of the parameters), hypothesis predicate name)
SPEC = {
    're': dict(params='x', start='Reset (2 * x + 36) T', end='S (x + 11) 1', pre=lambda e: 4 * e['x'] + 84),
    'ro': dict(params='x', start='Reset (2 * x + 37) T', end='S (x + 12) 1', pre=lambda e: 4 * e['x'] + 88),
    'g': dict(params='d b', start='S (d + 2) b T', end='S d (b + 3)', pre=lambda e: 4 * e['d'] + 4 * e['b'] + 48),
    'e0': dict(params='b', start='S 0 b T', end='Reset (2 * b + 20)', pre=lambda e: 4 * e['b'] + 42),
    'e1': dict(params='b', start='S 1 b T', end='Reset (2 * b + 23)', pre=lambda e: 4 * e['b'] + 48),
}


def tail_word(fin, pre):
    """The cells of the end configuration's right side after the first pre(env) cells, before the last context:
    the same for every value of the parameters (checked on a few)."""
    toks = fin.right[:-1]
    ws = set()
    for k in range(3, 8):
        env = {v: k + 2 * i for i, v in enumerate(sorted(fin.vars()))}
        env.update({v: k for v in 'xdb'})
        cells = expand(toks, env)
        ws.add(tuple(cells[pre(env):]))
    assert len(ws) == 1, ws
    return list(ws.pop())


def state(q):
    return '.' + q


def emit_composition(data):
    out = []
    for name in ('re', 'ro', 'g', 'e0', 'e1'):
        info, excs = data[name]
        sp = SPEC[name]
        w = tail_word(info[-1][1], sp['pre'])
        Ts = ['T'] + ['T%d' % (i + 1) for i in range(len(excs))]
        # the hypothesis
        hyp = []
        for i, (u, q, q2, v) in enumerate(excs):
            hyp.append('∃ %s, Exc %s %s %s %s %s %s ∧' % (Ts[i + 1], lean_list(u[::-1]), state(q), state(q2),
                                                     lean_list(v), Ts[i], Ts[i + 1]))
        doc = ('The tail excursions of the piece `%s_run`, in order, each from the tail the one before left; `K` '
               'receives the tail at the end.' % name)
        out.append('/-- %s -/\ndef H%s (T : Tape) (K : Tape → Prop) : Prop :=\n  %s K (app %s %s)\n' % (
            doc, name, ' '.join(hyp), lean_list(w), Ts[-1]))
        # the run
        pat = ', '.join('%s, ⟨n%d, e%d⟩' % (Ts[i + 1], i + 1, i + 1) for i in range(len(excs)))
        pat = '⟨' + (pat + ', ' if pat else '') + 'hK⟩'
        def seg(i):
            a, b = info[i]
            return '%s_s%d %s %s' % (name, i, ' '.join(sorted(a.vars() | b.vars())), Ts[i])
        chain = seg(len(excs))
        for i in reversed(range(len(excs))):
            u, rest = pop_cells(info[i][1].left, MLEN)
            chain = 'steps_seq trans (%s) (steps_seq trans (e%d (%s)) (%s))' % (
                seg(i), i + 1, symtm.left_term(rest), chain)
        binders = ' '.join('(%s : Nat)' % p for p in sp['params'].split())
        out.append('theorem %s_run %s (T : Tape) (K : Tape → Prop) (h : H%s T K) :\n'
                   '    ∃ T\', K T\' ∧ Plus trans (%s) (%s T\') := by\n'
                   '  obtain %s := h\n'
                   '  exact ⟨_, hK, plus_of (%s)\n'
                   '    (by tape_norm) (by tape_norm)⟩\n' % (
                       name, binders, name, sp['start'], sp['end'], pat, chain))
    return '\n'.join(out)


def emit_reach():
    out = []
    for start, name, who in (('A', 'own', 'this machine'), ('D', 'twin', 'the twin (this table started in D)')):
        s, X = [r for r in resets(start, 1e5) if r[1] >= 36][0]
        c = Conc(start)
        while c.st < s:
            c.step()
        lo, hi = min(c.t), max(c.t)
        l = [c.t.get(k, 0) for k in range(c.h - 1, lo - 1, -1)]
        r = [c.t.get(k, 0) for k in range(c.h, hi + 1)]
        assert l[0] == 1 and not any(l[1:]) and r[:2 + 2 * X] == [1, 0] + [1, 0] * X and r[2 + 2 * X:4 + 2 * X] != [1, 0]
        rest = r[2 + 2 * X:]
        out.append('/-- The tail at the first reset with X >= 36 of %s. -/\ndef T0%s : Tape := app %s blank\n' % (
            who, name, lean_list(rest)))
        out.append('theorem fsteps_%s : fsteps %d (FCfg.blank .%s) = some ⟨%s, %s, .B⟩ := by\n  decide +kernel\n' % (
            name, s, start, lean_list(l), lean_list(r)))
        out.append('/-- %s is at `Reset %d T0%s` after %d steps from blank tape. -/\n'
                   'theorem reach_%s : steps %d (blankCfg .%s) = some (Reset %d T0%s) := by\n'
                   '  refine (blank_reaches trans fsteps_%s).trans ?_\n'
                   '  show some (⟨app (true :: List.replicate %d false) blank, _, _⟩ : Config) = _\n'
                   '  rw [app_cons, app_falses]\n'
                   '  rfl\n' % (who[0].upper() + who[1:], X, name, s, name, s, start, X, name, name, len(l) - 1))
    return '\n'.join(out)


def main():
    out = []
    data = {}
    n = check_generic_signature()
    for name in ('re', 'ro', 'e0', 'e1'):
        segs, excs = run_piece(name)
        data[name] = (emit_piece(name, segs, excs, out), excs)
    segs, excs = generic_piece()
    data['g'] = (emit_piece('g', segs, excs, out), excs)
    hdr = ('The head part of a phase of 1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---, cut at the excursions into the '
           'tail; written by `py/gen_resetmap.py` (bbtools.symtm.prove).  Each theorem is a run for every value '
           'of its parameters and every tail.  The composition is in `ResetMap.lean`.')
    if '--no-runs' not in sys.argv:
        txt = symtm.rules_file('Machine', 'H129771', out, hdr)
        txt = txt.replace('\nnamespace H129771\n', '\nset_option maxRecDepth 20000\n\nnamespace H129771\n', 1)
        txt = txt.replace('\nopen TM\n', '\nopen TM\n' + CROSS_R0, 1)
        open(os.path.join(here, '../lean/ResetMapRuns.lean'), 'w').write(txt)
    comp = emit_composition(data)
    src = open(os.path.join(here, '../lean/ResetMap.lean')).read()
    a, b = '-- BEGIN GENERATED (py/gen_resetmap.py)\n', '-- END GENERATED\n'
    src = src[:src.index(a) + len(a)] + comp + src[src.index(b):]
    a, b = '-- BEGIN REACH (py/gen_resetmap.py)\n', '-- END REACH\n'
    src = src[:src.index(a) + len(a)] + emit_reach() + src[src.index(b):]
    open(os.path.join(here, '../lean/ResetMap.lean'), 'w').write(src)
    print('generic phase steps checked: %d' % n, file=sys.stderr)


if __name__ == '__main__':
    main()
