"""Collisions with their gaps as variables: write lean/Collisions.lean.

    python3 holdouts/<M>/py/gen_collisions.py [MAXSTEPS]      (default 1e14: 25 s; 1.6e18: 20 min)

Runs the exact simulator (`mover_sim.py`) to MAXSTEPS and records every run it makes cell by cell (a *collision*),
grouped by the sequence of (state, symbol) pairs it reads, runs of pairs crossed by a rule counted as one token: a
*family*.  For each family seen, the first occurrence is turned into a symbolic configuration: every run of pairs
becomes `(01)^(a+k)` (or `(10)^(b+k)` on the right) with its own variable, `k` the least count the run needs, and
everything the run never looks at becomes a context (`L`, `R`).  `bbtools.symtm` runs it to the end of the collision
and writes the Lean proof, so each lemma holds for every value of every gap and every tape in the contexts.

The whole-tape runs, made when no mover lies between the two places where the head turns, are left out ("plain"); so is a family
that crosses more stored cells than the simulator keeps (it is listed at the end of the file).  At the right end a
collision may cross a list of swept movers `1 (10)^(g+2)`, any number of them, ending with `1 (10)^1` and blank tape:
the lemma stops at the second one, and `zb_cells` (one swept mover becomes a mover at rest) and `ze_cells` (the last
one) take over; `lean/ZList.lean` chains them over any list.
"""
import collections
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "../../../tools/py"))
import mover_sim as ms                                           # noqa: E402
from mover_sim import pop, push, push_gap, T, E_, C_, Halt, Boundary, MacroPoint   # noqa: E402
from bbtools.symtm import Config, Rep, Ctx, Blank, Lin, run, prove, rules_file, NeedSplit, Halted   # noqa: E402
from bbtools.machine import Machine                              # noqa: E402

M = ms.MACH
MACH = Machine.parse(M)
FAM = collections.OrderedDict()
CNT = collections.Counter()
KIND = collections.Counter()
CUR = [0]


def fmt(x):
    m, e = ('%.2g' % x).split('e+') if 'e+' in '%.2g' % x else ('%.2g' % x, None)
    return m + 'e' + str(int(e)) if e else m


def compress(sig, star=False):
    """A run's tokens with every repeated block of up to 12 tokens written once with its count (or `*`)."""
    out, i = [], 0
    while i < len(sig):
        best = None
        for P in range(1, 13):
            blk = sig[i:i + P]; r = 1
            while sig[i + r * P:i + (r + 1) * P] == blk:
                r += 1
            if r >= 2 and (best is None or r * P > best[0] * len(best[1])):
                best = (r, blk)
        if best:
            out.append('[%s]^%s' % (' '.join(best[1]), '*' if star else best[0])); i += best[0] * len(best[1])
        else:
            out.append(sig[i]); i += 1
    return ' '.join(out)


def snap(st, n=400):
    return ['M' if isinstance(t, tuple) else t for t in st[-n:]], len(st) > n


def run_local_rec(L, R, s, maxmoves, stop_rightend=False, macro=False, pending=False):
    """mover_sim.run_local, recording the family of each run and a snapshot of its first occurrence."""
    sL, dL = snap(L)
    sR, dR = snap(R)
    sig = []; steps = 0; moves = 0; s0 = s
    try:
        if pending:
            x = pop(L); push(R, x); sig.append('p')
        while True:
            if stop_rightend and moves > 0 and s == E_ and len(R) == 1 and R[0] == 'B':
                sig.append('$'); return steps, s
            if moves > maxmoves:
                raise RuntimeError('too long')
            moves += 1
            if R[-1] == 'X':
                sig.append('>'); return steps, s
            if s == E_ and isinstance(R[-1], int):
                g = R.pop(); push_gap(L, g); steps += 2 * g; sig.append('~'); continue
            if macro and L[-1] == 'X' and s == E_ and (R[-1] == '0' or R[-1] == 'B'):
                sig.append('M'); raise MacroPoint(steps)
            c = pop(R); tr = T[(s, c)]; sig.append('ABCDEF'[s] + str(c))
            if tr is None:
                raise Halt((steps,))
            w, d, ns = tr; steps += 1; s = ns
            if d > 0:
                push(L, w)
            else:
                push(R, w)
                if s == C_ and isinstance(L[-1], int):
                    g = L.pop(); push_gap(R, g); steps += 2 * g; sig.append('<')
                if L[-1] == 'X':
                    sig.append('|'); raise Boundary(steps, s)
                x = pop(L); push(R, x)
    finally:
        kind = 'macro' if not stop_rightend else ('Z' if macro else 'plain')
        key = kind + ':' + compress(sig)
        CNT[key] += 1
        KIND[kind + ':' + compress(sig, True)] += 1
        if key not in FAM:
            FAM[key] = dict(kind=kind, L=sL, Ldeep=dL, R=sR, s0=s0, pending=pending, sig=sig, step=CUR[0])


# ---------------------------------------------------------------- symbolic generalisation
def build(f, depth, offs, fixed):
    vals = {}
    items = f['L'][-depth:]
    for i in range(len(items) - 1, -1, -1):
        if items[i] == 'M':
            items = items[i + 1:]; break
    left = []
    if items and items[0] in ('X', 'B'):
        left.append(Ctx('L') if items[0] == 'X' else Blank()); items = items[1:]
    else:
        left.append(Ctx('L'))

    def num(v, nm):
        vals[nm] = v
        return Lin(v) if nm in fixed else Lin(nm) + offs.get(nm, 1)
    for j, t in enumerate(items):
        if isinstance(t, int):
            left.append(Rep((0, 1), num(t, 'a%d' % (len(items) - 1 - j))))
        else:
            left.append(int(t))
    right = []
    RR = list(reversed(f['R']))
    for j, t in enumerate(RR):
        if f['kind'] == 'Z' and j >= 2 and t == '1' and j + 1 < len(RR) and isinstance(RR[j + 1], int):
            right.append(Ctx('R')); break          # a list of swept movers: ZList.lean
        if isinstance(t, int):
            right.append(Rep((1, 0), num(t, 'b%d' % j)))
        elif t in ('0', '1'):
            right.append(int(t))
        elif t == 'B':
            right.append(Blank()); break
        else:
            right.append(Ctx('R')); break
    if not isinstance(right[-1], (Ctx, Blank)):
        right.append(Ctx('R'))
    if f['pending']:                               # the head is on the last cell of the left part
        t = left[-1]
        if isinstance(t, int):
            left = left[:-1]; x = t
        else:
            k = t.n - 1
            left = left[:-1] + ([Rep(t.word, k)] if not k.is_zero() else []) + list(t.word[:-1]); x = t.word[-1]
        right = [x] + right
    return Config(left, f['s0'], right), vals


def at_end(c):
    if c.steps.is_zero():
        return False
    return (isinstance(c.right[0], Ctx) or (c.left and isinstance(c.left[-1], Ctx))
            or (c.state == E_ and len(c.right) == 1 and isinstance(c.right[0], Blank)))


def complete(f, fin):
    last = f['sig'][-1]
    if last in ('|', 'M'):
        return isinstance(fin.left[-1], Ctx)
    return not isinstance(fin.left[-1], Ctx)


def generalise(f):
    depth, offs, fixed = 6, {}, set()
    for _ in range(2000):
        cfg, vals = build(f, depth, offs, fixed)
        try:
            fin = run(MACH, cfg.copy(), at_end, max_moves=50000, rotate=True)
        except NeedSplit as e:
            nm = re.findall(r'[ab]\d+', str(e))[0]
            if vals[nm] > offs.get(nm, 1):
                offs[nm] = offs.get(nm, 1) + 1
            else:
                fixed.add(nm)
            continue
        if not complete(f, fin):
            if depth >= len(f['L']):
                return None
            depth *= 2; continue
        return cfg, fin
    return None


RULES = [
    ("zb_cells", "L E> 1 (10)^n+2 R", "L 0 0 1 1 0 (01)^n E> R",
     "At the right end the left part's sweep turns a swept mover `1 (10)^(n+2)` into a mover at rest with gap n."),
    ("ze_cells", "L E> 1 1 0 1 0^inf", "L 0 0 1 1 0 E> 0^inf",
     "The last swept mover, with a one-pair gap, becomes a mover at rest with no gap, and the head is at the right end."),
]

if __name__ == '__main__':
    stop = float(sys.argv[1]) if len(sys.argv) > 1 else 1e14
    ms.run_local = run_local_rec
    S = ms.start()
    while S.steps < stop:
        CUR[0] = S.steps; S.bounce()
    ths, seen, left_out, n = [], {}, [], 0
    for key in sorted(FAM, key=lambda k: -CNT[k]):
        f = FAM[key]
        if f['kind'] == 'plain':
            continue
        r = generalise(f)
        if r is None:
            left_out.append(key); continue
        cfg, fin = r
        sk = (str(cfg), str(fin))
        if sk in seen:
            seen[sk][1] += CNT[key]; continue
        n += 1
        seen[sk] = [n, CNT[key], f]
    for (s_, e_), (i, cnt, f) in sorted(seen.items(), key=lambda kv: kv[1][0]):
        cfg, fin = generalise(f)
        doc = ("Collision %d (%s, %d time%s up to step %s, first at step %d): `%s` becomes `%s`."
               % (i, f['kind'], cnt, '' if cnt == 1 else 's', fmt(stop), f['step'], cfg, fin))
        txt, _ = prove(MACH, 'col%d' % i, cfg, fin, doc=doc, rotate=True, count_first=True, max_seg=400,
                       max_moves=50000)
        ths.append(txt)
    for name, s_, e_, doc in RULES:
        ths.append(prove(MACH, name, s_, e_, doc=doc)[0])
    note = ("Collisions of %s, written by `py/gen_collisions.py` (%d families up to step %s, %d lemmas)."
            % (M, sum(1 for k in FAM if FAM[k]['kind'] != 'plain'), fmt(stop), n))
    if left_out:
        note += " Left out: " + "; ".join("`%s` (%d time%s)" % (k[:80] + '…', CNT[k], '' if CNT[k] == 1 else 's')
                                          for k in left_out) + "."
    open(os.path.join(HERE, "../lean/Collisions.lean"), "w").write(rules_file("Machine", "H71372", ths, note))
    print("wrote lean/Collisions.lean:", n, "lemmas,", len(left_out), "left out,",
          sum(1 for k in FAM if FAM[k]['kind'] == 'plain'), "plain families")
