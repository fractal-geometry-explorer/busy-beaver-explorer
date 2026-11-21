#!/usr/bin/env python3
"""The exact sweep rules of the digit model, split into a stop rule and a carry chain (21 November 2026).

cdigits.SPEC.memo holds every window rule the long runs derive: a symbolic run of the machine on a window (the
carry chain at the bottom, its stop digit, more digits when the run reaches them), long runs as variables.  This
script dumps that memo from a run (`dump`) and sorts the rules (`table`):

  * rules whose walls are all Z, O, T: checked against the generic counter rule (chain T digits become Z with the
    same runs, the stop digit goes up by one, the top chain digit loses 1 block (stop Z) or 2 (stop O), the end run
    gains 2, steps 12 per block and 16 per chain digit, plus 12 per block of the end run and 20 or 18);
  * all rules, as (stop part, chain length): the stop part's changes and step constant must not depend on the chain.

    python3 py/ruletable.py dump b1|b2 CKPT.pkl SECONDS OUT.pkl   (kill -USR1 writes OUT.pkl.part on the way)
    python3 py/ruletable.py table b1|b2 MEMO.pkl
"""
import collections
import os
import pickle
import signal
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lean  # noqa: E402

ZOT = 'ZOT'


def dump(mach, ckpt, secs, out):
    lean.C.use(mach)

    def _dump(*a):
        pickle.dump(dict(lean.C.SPEC.memo), open(out + '.part', 'wb'))
        print('dumped', len(lean.C.SPEC.memo), flush=True)

    def _term(*a):
        raise SystemExit
    signal.signal(signal.SIGUSR1, _dump)
    signal.signal(signal.SIGTERM, _term)
    st, T, nsw = lean.load(ckpt)
    try:
        lean.advance(st, T, nsw, None, seconds=secs, log=open(os.devnull, 'w'))
    finally:
        pickle.dump(dict(lean.C.SPEC.memo), open(out, 'wb'))
        print('saved', len(lean.C.SPEC.memo), flush=True)


def table(mach, path):
    lean.C.use(mach)
    m = pickle.load(open(path, 'rb'))
    def ev(l, env): return l[0] + sum(a * env[v] for v, a in l[1].items())
    def evs(s, env): return s.k + sum(a * env.get(v, 0) for v, a in s.c.items())
    pats = collections.Counter(); ex = {}
    other = collections.Counter()
    for key, res in m.items():
        if res[0] != 'ok':
            continue
        usepre, rd, lb, end = key
        nctx, nd, nl, nend, steps = res[1]
        if len(nd) != len(rd) or not all(w in ZOT for w, _ in rd) or not all(w in ZOT for w, _ in nd):
            other[('shape', usepre, end, tuple(w for w, _ in rd), tuple(w for w, _ in nd))] += 1
            continue
        rows = []
        for env in ({'z': 50, **{'v%d' % i: 40 + 7 * i for i in range(len(rd))}}, {'z': 91, **{'v%d' % i: 63 + 11 * i for i in range(len(rd))}}):
            runs = [(b[1] + env['v%d' % i]) if isinstance(b, tuple) else b for i, (w, b) in enumerate(rd)]
            last = (lb[1] + env['z']) if isinstance(lb, tuple) else lb
            out = [ev(l, env) for _, l in nd]
            rows.append((runs, last, out, ev(nl, env), evs(steps, env)))
        n = len(rd); j = 0
        while j < n and rd[n - 1 - j][0] == 'T':
            j += 1
        sidx = n - 1 - j
        inw = [w for w, _ in rd]; outw = [w for w, _ in nd]
        pred = list(inw)
        for q in range(sidx + 1, n): pred[q] = 'Z'
        if sidx >= 0: pred[sidx] = ZOT[ZOT.index(inw[sidx]) + 1] if inw[sidx] != 'T' else '?'
        wall_ok = pred == outw
        d = tuple(o - r for o, r in zip(rows[0][2], rows[0][0]))
        d2 = tuple(o - r for o, r in zip(rows[1][2], rows[1][0]))
        dl = rows[0][3] - rows[0][1]; dl2 = rows[1][3] - rows[1][1]
        # steps minus 12r+16 over the chain runs
        base = [rows[t][4] - sum(12 * rows[t][0][q] + 16 for q in range(sidx + 1, n)) - 12 * rows[t][1] for t in (0, 1)]
        stopw = inw[sidx] if sidx >= 0 else None
        pat = (wall_ok, usepre, end, nend, stopw, j, d == d2 and d, dl == dl2 and dl, base[0] == base[1] and base[0])
        pats[pat] += 1
        ex.setdefault(pat, key)
    print('rules', len(m), 'ok', sum(1 for v in m.values() if v[0] == 'ok'))
    print('-- Z/O/T rules: (walls as counter rule, whole-tape, end, new end, stop, chain, run changes, last change, step constant)')
    for p, c in sorted(pats.items(), key=lambda x: -x[1]):
        print(c, p)
    print('-- other rules')
    for p, c in sorted(other.items(), key=lambda x: -x[1])[:60]:
        print(c, p)
    print('-- every rule, as stop part + T chain: does the stop part not depend on the chain length?')
    grp = collections.defaultdict(set)
    for key, res in m.items():
        if res[0] != 'ok':
            continue
        usepre, rd, lb, end = key
        nctx, nd, nl, nend, steps = res[1]
        n = len(rd); j = 0
        while j < n and rd[n - 1 - j][0] == 'T':
            j += 1
        k = 0
        while k < len(nd) and nd[len(nd) - 1 - k][0] == 'Z' and k < j:
            k += 1
        if k != j:
            grp[('chain not all Z', key)].add(None); continue
        env = {'z': 50, **{'v%d' % i: 40 + 7 * i for i in range(n)}}
        runs = [(b[1] + env['v%d' % i]) if isinstance(b, tuple) else b for i, (w, b) in enumerate(rd)]
        last = (lb[1] + env['z']) if isinstance(lb, tuple) else lb
        out = [ev(l, env) for _, l in nd]
        hi_in, hi_out = rd[:n - j], nd[:len(nd) - j]
        # chain digits: out run - in run; first chain digit may lose f
        cd = tuple(out[len(nd) - j + q] - runs[n - j + q] for q in range(j))
        top = (out[0] - runs[0]) if hi_out and hi_in and len(hi_in) == len(hi_out) else None
        env2 = {kk: vv + 1 for kk, vv in env.items()}
        coef = {}
        for q in range(n):
            if isinstance(rd[q][1], tuple):
                e3 = dict(env); e3['v%d' % q] += 1; coef[q] = evs(steps, e3) - evs(steps, env)
        if isinstance(lb, tuple):
            e3 = dict(env); e3['z'] += 1; coef['z'] = evs(steps, e3) - evs(steps, env)
        cc = set(coef.get(q) for q in range(n - j, n) if q in coef)
        c = cc.pop() if len(cc) == 1 else (12 if not cc else None)
        stp = (c, coef.get('z'), evs(steps, env) - sum(c * runs[q] + 16 for q in range(n - j, n)) - (coef.get('z') or 0) * last) if c is not None else ('mixed', tuple(sorted(cc)))
        sig = (tuple(w for w, _ in hi_in), tuple(b if not isinstance(b, tuple) else 'v' for _, b in hi_in), tuple(w for w, _ in hi_out), end, nend, cd[:1], all(x == 0 for x in cd[1:]), ev(nl, env) - last if j else None, stp)
        grp[sig[:5]].add((j > 0, sig[5:]))
    for g, s in sorted(grp.items(), key=lambda x: str(x[0])):
        print(g, sorted(s, key=str))


if __name__ == '__main__':
    if sys.argv[1] == 'dump':
        dump(sys.argv[2], sys.argv[3], float(sys.argv[4]), sys.argv[5])
    else:
        table(sys.argv[2], sys.argv[3])
