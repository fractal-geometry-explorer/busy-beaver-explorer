"""Find the phase rules (one period of each kind of phase) that the exact accelerated run uses, with the smallest
thresholds, in bbtools.symtm notation (input for rules.py, which proves them in Lean).

usage (from the repo root):
  python3 holdouts/1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---/py/phase_rules.py MACHINE LO HI [MAXRULES]
prints, per kind of phase (the nonzero count changes), the rule used most often after step LO (run up to HI).
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import accel  # noqa: E402
from accel import Rep, Lin, BL  # noqa: E402
from bbtools.symtm import parse_lin  # noqa: E402


def parse(m, s):
    parts = s.split()
    i = next(k for k, p in enumerate(parts) if p.endswith('>') and len(p) == 2)
    st = 'ABCDEF'.index(parts[i][0])

    def toks(ps):
        out = []
        for p in ps:
            if p == '0^inf':
                out.append(BL)
            elif p.startswith('('):
                w, e = p[1:].split(')^')
                out.append(Rep(tuple(int(ch) for ch in w), parse_lin(e)))
            else:
                out.extend(int(ch) for ch in p)
        return out
    L = toks(parts[:i])
    R = list(reversed(toks(parts[i + 1:])))
    return accel.Cfg(m, L, st, R, Lin(0))


def period(m, s, level=0, maxmoves=2 * 10 ** 6):
    """symbolic run from configuration string s to the first recurrence of its key; (end string, deltas, steps)"""
    for ev in 'XLR':
        try:
            r = _period(m, s, ev, level, maxmoves)
        except accel.NeedSplit:
            r = None
        if r:
            return r
    return None


def _period(m, s, ev, level, maxmoves):
    c = parse(m, s)
    c.ev = ev
    k0 = accel.key_of(c, level)
    start = [z.n for z in accel.reps(c)]
    mv = 0
    while True:
        mv += 1
        if accel.advance(c) and accel.key_of(c, level) == k0:
            break
        if mv > maxmoves:
            return None
    end = [z.n for z in accel.reps(c)]
    d = []
    for a, b in zip(start, end):
        x = Lin(b) - Lin(a)
        if not x.is_const():
            return None
        d.append(x.k)
    return accel.symtm_str(c), d, c.steps


def minimise(m, s, d0):
    """lower each block's constant as far as the period still holds with the same changes"""
    toks = s.split()
    idx = [i for i, t in enumerate(toks) if t.startswith('(') and '+' in t.split(')^')[1]]
    for i in idx:
        w, e = toks[i].split(')^')
        v, k = e.split('+')
        lo, hi = 0, int(k)
        while lo < hi:
            mid = (lo + hi) // 2
            t2 = list(toks)
            t2[i] = '%s)^%s+%d' % (w, v, mid)
            try:
                r = period(m, ' '.join(t2))
            except accel.NeedSplit:
                r = None
            if r and r[1] == d0:
                hi = mid
            else:
                lo = mid + 1
        toks[i] = '%s)^%s+%d' % (w, v, lo)
    s2 = ' '.join(toks)
    return s2, period(m, s2)


def main():
    M = sys.argv[1]
    lo, hi = float(sys.argv[2]), float(sys.argv[3])
    nmax = int(sys.argv[4]) if len(sys.argv) > 4 else 12
    S = accel.Sim(M)
    seen = {}

    def oj(rule, k):
        if S.c.steps < lo:
            return
        d = tuple(x for x in rule[2] if x)
        e = seen.setdefault(d, {})
        key = rule[4]
        e[key] = e.get(key, 0) + 1
    S.on_jump = oj
    S.run(hi)
    out = sorted(seen.items(), key=lambda x: -sum(x[1].values()))[:nmax]
    for d, rules in out:
        (st, en), n = max(rules.items(), key=lambda x: x[1])
        r0 = period(S.m, st)
        s2, (e2, d2, steps) = minimise(S.m, st, r0[1])
        print('# changes %s, used %d times after step %.0e; %s steps' % (d, sum(rules.values()), lo, steps))
        print(repr((s2, e2)) + ',')


if __name__ == '__main__':
    main()
