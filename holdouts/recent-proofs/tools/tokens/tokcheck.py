#!/usr/bin/env python3
"""tokcheck: independent checker for certificates written by tokgram (CERT=file).

A certificate is a finite object:
  - a right-linear grammar over runs: nonterminal N -> (bit, length code, N'), and the end symbol (blank tape);
    a length code c < cap means exactly c cells, cap + p means "at least cap cells, parity p";
  - half tapes: a few explicit runs followed by a nonterminal; it stands for a set of cell strings;
  - calls (ctx, state, half tape) with their facts: (return state, half tape);
  - top configurations: exact cells x from the leftmost 1, head offset h, state, half tape after x.
The checker verifies
  1. the real configuration at the seed step is one of the top configurations;
  2. one machine step from any top configuration leads to top configurations again, never to a halt,
     where a move off the right end of x is answered by the facts of a call;
  3. for every call, running the machine on the context and the half tape, with nested calls answered by
     their facts, never halts, and every way of leaving the context to the left is one of the call's facts.
"Is one of" means: same explicit data, and the half tape is covered (its explicit runs extend the listed ones
along productions of the grammar and end in the same nonterminal).
By induction on the number of steps, 1 to 3 imply that the machine never halts.
Usage: tokcheck.py CERTFILE"""
import sys
from collections import defaultdict

def main(fn):
    L = open(fn).read().split('\n')
    assert L[0].startswith('tokgram-certificate 1')
    hdr = {}; i = 1
    while not L[i][:2] in ('N ', 'T ', 'C '):
        k, v = L[i].split(' ', 1); hdr[k] = v; i += 1
    m = hdr['machine']; mirror = hdr['mirror'] == '1'; CAP = int(hdr['cap']); W = int(hdr['window']); J = int(hdr['context']); seedstep = int(hdr['seedstep'])
    TM = {}
    for s, row in enumerate(m.split('_')):
        for b in range(2):
            t = row[3 * b:3 * b + 3]
            if t[0] == '-': TM[(s, b)] = None
            else:
                d = 1 if t[1] == 'R' else -1
                TM[(s, b)] = (int(t[0]), -d if mirror else d, ord(t[2]) - 65)
    prods = defaultdict(list); END = None
    def parse_runs(txt):
        v = [int(z) for z in txt.split()]
        b0 = v[0]; return tuple((b0 ^ (k & 1), c) for k, c in enumerate(v[1:]))
    calls = defaultdict(list); tops = defaultdict(list); ntop = ncall = nfact = 0
    for ln in L[i:]:
        if not ln: continue
        if ln[0] == 'N':
            a, b = ln[2:].split(':'); a = a.split(); n = int(a[0])
            if len(a) > 1: END = n
            v = [int(z) for z in b.split()]
            prods[n] = [(v[k], v[k + 1], v[k + 2]) for k in range(0, len(v), 3)]
        elif ln[0] == 'T':
            a, r, n = ln[2:].split(';'); x, h, st = a.split(); x = '' if x == '-' else x
            tops[(x, int(h), ord(st) - 65)].append((parse_runs(r), int(n))); ntop += 1
        elif ln[0] == 'C':
            key, facts = ln[2:].split(':'); c, st, r, n = key.split(';')
            fl = []
            for f in facts.split('/'):
                if not f.strip(): continue
                s2, r2, n2 = f.split(';'); fl.append((ord(s2.strip()) - 65, (parse_runs(r2), int(n2)))); nfact += 1
            calls[(parse_runs(c), ord(st.strip()) - 65)].append(((parse_runs(r), int(n)), fl)); ncall += 1
    assert END is not None
    BLANK = ((), END)

    def inc(c): return c + 1 if c < CAP - 1 else (CAP + (CAP & 1) if c == CAP - 1 else CAP + ((c - CAP) ^ 1))
    def dec(c):
        """possible codes after removing one cell; 0 = the run is gone"""
        if c < CAP: return [c - 1]
        par = c - CAP; out = [CAP + (par ^ 1)]
        if (CAP - 1) & 1 == par ^ 1: out.append(CAP - 1)
        return out
    def first(a): return a[0][0][0] if a[0] else 0
    def uncons(a):
        runs, n = a
        if not runs:
            assert n == END; return [a]
        (bit, c) = runs[0]; out = []
        for c2 in dec(c):
            if c2 > 0: out.append((((bit, c2),) + runs[1:], n))
            elif len(runs) > 1: out.append((runs[1:], n))
            elif n == END: out.append(BLANK)
            else:
                for (b2, c3, n2) in prods[n]: out.append((((b2, c3),), n2))
        return out
    def cons(c, a):
        runs, n = a
        if not runs:
            assert n == END
            return a if c == 0 else (((1, 1),), END)
        if runs[0][0] == c: return (((c, inc(runs[0][1])),) + runs[1:], n)
        return (((c, 1),) + runs, n)
    def pushl(l, c):
        if l and l[0][0] == c: return ((c, inc(l[0][1])),) + l[1:]
        return ((c, 1),) + l
    def popl(l):
        (bit, c) = l[0]; out = []
        for c2 in dec(c): out.append((((bit, c2),) + l[1:]) if c2 > 0 else l[1:])
        return out
    def covers(a, b):
        """every cell string of b is a cell string of a (syntactic sufficient condition)"""
        ra, na = a; rb, nb = b
        if len(ra) > len(rb) or rb[:len(ra)] != ra: return False
        cur = {na}
        for (bit, c) in rb[len(ra):]:
            cur = {n2 for n in cur for (b2, c2, n2) in prods[n] if b2 == bit and c2 == c}
            if not cur: return False
        return nb in cur
    def find_call(ctx, s, b):
        lst = calls.get((ctx, s), ())
        for (a, fl) in lst:          # the call itself, if listed
            if a == b: return fl
        for (a, fl) in lst:          # otherwise any listed call that covers it
            if covers(a, b): return fl
        return None
    def top_ok(x, h, s, b):
        if b == BLANK:
            x = x.rstrip('0')
        if x == '' and b == BLANK: h = 0
        return any(covers(a, b) for a in tops.get((x, h, s), ()))

    # 3. calls
    for (ctx0, s0), lst in calls.items():
        for (a0, facts) in lst:
            seen = set(); st = [(ctx0, s0, a0)]; seen.add(st[0])
            def land(l, q, b):
                if not l:
                    if not any(q == q2 and covers(a2, b) for (q2, a2) in facts):
                        raise SystemExit('FAIL: call %r %s %r has an unlisted return %s %r' % (ctx0, chr(65 + s0), a0, chr(65 + q), b))
                    return
                x = l[0][0]; b2 = cons(x, b)
                for l2 in popl(l):
                    t = (l2, q, b2)
                    if t not in seen: seen.add(t); st.append(t)
            while st:
                l, q, b = st.pop()
                c = first(b); rests = uncons(b)
                tr = TM[(q, c)]
                if tr is None:
                    if not rests: continue
                    raise SystemExit('FAIL: halt inside call %r %s %r' % (ctx0, chr(65 + s0), a0))
                w, d, q2 = tr
                for b1 in rests:
                    if d < 0: land(l, q2, cons(w, b1))
                    else:
                        l2 = pushl(l, w)
                        if len(l2) <= J:
                            t = (l2, q2, b1)
                            if t not in seen: seen.add(t); st.append(t)
                        else:
                            fl = find_call(l2[:J], q2, b1)
                            if fl is None: raise SystemExit('FAIL: nested call missing: %r %s %r' % (l2[:J], chr(65 + q2), b1))
                            for (q3, a3) in fl: land(l2[J:], q3, a3)
    # 2. top level
    for (x, h, s), lst in tops.items():
        for a in lst:
            n = len(x); c = int(x[h]) if 0 <= h < n else 0
            tr = TM[(s, c)]
            if tr is None: raise SystemExit('FAIL: halt at top configuration %r' % ((x, h, s, a),))
            w, d, s2 = tr; cands = []
            if 0 <= h < n:
                y = x[:h] + str(w) + x[h + 1:]
                if y[0] == '0':
                    z = y.find('1')
                    if z >= 0: cands.append((y[z:], h - z, a))
                    else:
                        hh = h - n; seen = {(a, 0)}; st = [(a, 0)]
                        while st:
                            b, z2 = st.pop()
                            if b == BLANK: cands.append(('', 0, BLANK)); continue
                            if z2 > 4 * W + 64: raise SystemExit('FAIL: unbounded gap')
                            for b1 in uncons(b):
                                if first(b) == 1: cands.append(('1', hh - z2, b1))
                                elif (b1, z2 + 1) not in seen: seen.add((b1, z2 + 1)); st.append((b1, z2 + 1))
                else: cands.append((y, h, a))
            elif h < 0:
                cands.append((('1' + '0' * (-h - 1) + x, 0, a) if w == 1 else (x, h, a)))
            else:
                assert n == 0
                cands.append((('1', 0, a) if w == 1 else (x, h, a)))
            for (y, hh, b) in cands:
                while len(y) > W: b = cons(int(y[-1]), b); y = y[:-1]
                if y == '':
                    if not top_ok(y, 0, s2, b): raise SystemExit('FAIL: top successor missing %r' % ((y, 0, s2, b),))
                    continue
                nh = hh + d
                if nh < len(y):
                    if not top_ok(y, nh, s2, b): raise SystemExit('FAIL: top successor missing %r from %r' % ((y, nh, s2, b), (x, h, s, a)))
                    continue
                fl = find_call((), s2, b)
                if fl is None: raise SystemExit('FAIL: top call missing %r' % ((s2, b),))
                for (q3, a3) in fl:
                    if not top_ok(y, len(y) - 1, q3, a3): raise SystemExit('FAIL: top successor missing after call %r' % ((y, len(y) - 1, q3, a3),))
    # 1. seed
    tape = defaultdict(int); p = 0; s = 0
    for _ in range(seedstep):
        tr = TM[(s, tape[p])]
        if tr is None: raise SystemExit('FAIL: the machine halts before the seed step')
        tape[p] = tr[0]; p += tr[1]; s = tr[2]
    ones = [k for k, v in tape.items() if v]
    ok = False
    if not ones: ok = top_ok('', 0, s, BLANK)
    else:
        E = min(ones); last = max(ones); h = p - E
        for (x, h2, s2), lst in tops.items():
            if s2 != s or h2 != h or len(x) > last - E + 1: continue
            if any(tape[E + k] != int(ch) for k, ch in enumerate(x)): continue
            # the rest as maximal runs with exact lengths
            cells = [tape[k] for k in range(E + len(x), last + 1)]
            runs = []
            for c in cells:
                if runs and runs[-1][0] == c: runs[-1][1] += 1
                else: runs.append([c, 1])
            target = tuple((b, n if n < CAP else CAP + (n & 1)) for b, n in runs)
            if any(covers(a, (target, END)) for a in lst): ok = True; break
    if not ok: raise SystemExit('FAIL: the seed configuration is not a top configuration')
    print('OK %s: %d nonterminals, %d calls, %d facts, %d top configurations; seed step %d' % (m, len(prods), ncall, nfact, ntop, seedstep))

if __name__ == '__main__':
    main(sys.argv[1])
