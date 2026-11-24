"""Event rules of a two-counter hub machine (the models of cjump.py), proved in Lean with symtm.

A hub event (state S reading r at P, period 1) changes the lowest digits of the left counter and of the right
counter.  `sample_rules` samples real events from a direct run, groups them by the cells they touch, and proves one
rule per group: when the left counter borrows, through `k` digits with `k` a variable (the left digits `p q^k q0`
becoming `q p^k p0`) and the touched right cells literal; otherwise with all touched cells literal.
`carry_rules` takes two literal rules that differ by one inserted word and proves the rule with that word repeated
`j` times (the right counter carrying through `j` digits).  `lean_file` puts a borrow rule, two carry rules and the
most frequent literal rule into one Lean file.  Lean is the judge: every rule is a theorem about every tape beyond
the cells shown.

usage: python3 -m bbtools.hubrules MACHINE AT "(P,S,r)" "(a,w0,p0,q0,w,p,q)" NAMESPACE > Counter.lean
       (run from tools/py; AT a step count at which the model holds, the left side model as printed by cjump.py)
"""
import sys, re, ast, io, collections, contextlib
from . import symtm
from . import cjump as C


def events(tm, at, key, nev):
    T = C.parse_tm(tm)
    sim = C.Sim(tm); sim.run(int(at)); sim.run(sim.steps + 10 ** 10, key=key)
    P, S, R = key
    out = []
    for _ in range(nev):
        lo, hi = sim.lo - 2, sim.hi + 2
        before = sim.seg(lo, hi); mn = mx = sim.head; st0 = sim.steps; first = True
        while True:
            r = sim.c[sim.head + sim.off]
            if not first and (sim.head, sim.state, r) == (P, S, R): break
            first = False
            t = T[(sim.state, r)]
            if t is None: return out, 'halt'
            sim.c[sim.head + sim.off] = t[0]; sim.head += t[1]; sim.state = t[2]; sim.steps += 1
            if sim.head < sim.lo: sim.lo = sim.head
            if sim.head > sim.hi: sim.hi = sim.head
            mn = min(mn, sim.head); mx = max(mx, sim.head)
        after = sim.seg(lo, hi)
        out.append((lo, before, after, mn, mx, sim.steps - st0))
    return out, None

def sample_rules(tm, at, key, L, nev=3000, maxrules=12):
    P, S, R = key
    a, w0, p0, q0, w, p, q = L
    St = 'ABCDEF'[S]
    evs, h = events(tm, at, key, nev)
    pats = collections.Counter(); ex2 = {}
    for lo, b, af, mn, mx, n in evs:
        cell = lambda t, x: str(t[x - lo])
        # left: count borrow length from the hub
        if ''.join(cell(b, x) for x in range(a - w0, a)) != q0:
            key2 = ('nolow', ''.join(cell(b, x) for x in range(mn, a)))
            k = ''.join(cell(af, x) for x in range(mn, a))
        else:
            k = 0; x = a - w0
            while ''.join(cell(b, y) for y in range(x - w, x)) == q: k += 1; x -= w
            if ''.join(cell(b, y) for y in range(x - w, x)) != p: continue
            x -= w
            extra = ''.join(cell(b, y) for y in range(mn, x)) if mn < x else ''
            key2 = ('borrow', extra)
        rw = ''.join(cell(b, y) for y in range(a, mx + 1))
        rwa = ''.join(cell(af, y) for y in range(a, mx + 1))
        kk = (key2, rw, rwa)
        pats[kk] += 1; ex2.setdefault(kk, k)
    print(len(evs), 'events,', len(pats), 'patterns', file=sys.stderr)
    thms = []; cover = 0
    for (key2, rw, rwa), cnt in pats.most_common(maxrules):
        kind, extra = key2
        ii = P - a
        hubL, hubR = rw[:ii], rw[ii:]
        hubLa, hubRa = rwa[:ii], rwa[ii:]
        sp = lambda s: ' '.join(s)
        if kind == 'borrow':
            st = f"L {sp(extra)} {p} ({q})^k {q0} {sp(hubL)} {St}> {sp(hubR)} R"
            en = f"L {sp(extra)} {q} ({p})^k {p0} {sp(hubLa)} {St}> {sp(hubRa)} R"
        else:
            lw = extra; n0 = len(lw)
            # the same cells after: the left window keeps its length
            st = f"L {sp(lw)} {sp(hubL)} {St}> {sp(hubR)} R"
            en = None
        if en is None:
            lw2 = ex2[(key2, rw, rwa)]
            en = f"L {sp(lw2)} {sp(hubLa)} {St}> {sp(hubRa)} R"
        st = ' '.join(st.split()); en = ' '.join(en.split())
        name = f"event_{len(thms)}"
        try:
            txt, fin = symtm.prove(tm, name, st, en, rotate=True, count_first=True, max_seg=40,
                                   doc=f"{cnt} of {len(evs)} sampled events" + (": the left counter borrows through k digits" if kind == 'borrow' else ""))
            thms.append(txt); cover += cnt
            print('OK', cnt, st, '->', fin, 'steps', fin.steps, file=sys.stderr)
        except Exception as e:
            print('ERR', cnt, st, '|', en, e, file=sys.stderr)
    print('covered', cover, 'of', len(evs), file=sys.stderr)
    return thms


def _parse(line):
    m = re.match(r"OK (\d+) L (.*?) ([A-F])> (.*?) R -> L (.*?) ([A-F])> (.*?) R steps", line)
    if not m: return None
    cnt, l1, s1, r1, l2, s2, r2 = m.groups()
    j = lambda s: s.replace(' ', '')
    return int(cnt), j(l1), s1, j(r1), j(l2), j(r2)

def carry_rules(tm, lines):
    pats = [p for p in map(_parse, lines) if p and '(' not in p[1] + p[3]]
    out = []
    for A in pats:
        done = False
        for B in pats:
            if done: break
            if B[1] != A[1] or B[4] != A[4]: continue
            d = len(B[3]) - len(A[3])
            if not (3 <= d <= 10): continue
            for i in range(len(A[3]) + 1):
                if done: break
                u = B[3][i:i + d]
                if B[3] != A[3][:i] + u + A[3][i:]: continue
                for i2 in range(len(A[5]) + 1):
                    if done: break
                    v = B[5][i2:i2 + d]
                    if B[5] != A[5][:i2] + v + A[5][i2:]: continue
                    sp = lambda s: ' '.join(s)
                    st = f"L {sp(A[1])} {A[2]}> {sp(A[3][:i])} ({u})^j {sp(A[3][i:])} R"
                    en = f"L {sp(A[4])} {A[2]}> {sp(A[5][:i2])} ({v})^j {sp(A[5][i2:])} R"
                    st = ' '.join(st.split()); en = ' '.join(en.split())
                    if any(st == o[0] for o in out): continue
                    try:
                        txt, fin = symtm.prove(tm, 'carry', st, en, rotate=True, count_first=True, max_seg=40)
                        out.append((st, en, txt, fin)); done = True
                        print('OK', st, '->', fin, fin.steps, file=sys.stderr)
                    except Exception as e:
                        pass
    return out


def _rename(t, name, doc):
    t = re.sub(r"/-- .*? -/\n", "", t, count=1, flags=re.S)
    t = re.sub(r"theorem \w+", f"theorem {name}", t, count=1)
    return f"/-- {doc} -/\n" + t


def lean_file(tm, at, key, L, ns, nev=4000, where="py/rules.py"):
    err = io.StringIO()
    with contextlib.redirect_stderr(err):
        thms = sample_rules(tm, at, key, L, nev=nev, maxrules=30)
        log = err.getvalue().splitlines()
        cr = carry_rules(tm, log)
    out = []
    for t in [t for t in thms if '(k : Nat)' in t][:1]:
        out.append(_rename(t, 'borrow', 'The left counter borrows through `k` digits (its lowest digit was 0); the '
                                        'right counter changes only next to the hub.'))
    for i, (st, en, t, fin) in enumerate(cr[:2]):
        out.append(_rename(t, f'carry{i}', "The right counter carries through `j` digits"
                           + (" beyond a stretch of literal cells" if i else "") + " (the left counter's lowest digit was 1)."))
    for t in [t for t in thms if '(k : Nat)' not in t][:1]:
        out.append(_rename(t, 'plain', 'The most frequent sampled event without a long borrow, all cells literal.'))
    stats = [l for l in log if l.startswith('covered') or 'events,' in l]
    doc = (f"Counter rules of {tm}: one hub event with the left counter borrowing through `k` digits, and with the "
           f"right\ncounter carrying through `j` digits, for every `k`, `j` and every tape beyond the cells shown "
           f"(`L`, `R`).\nFound from {nev} sampled events by `{where}` of this folder (`tools/py/bbtools/hubrules.py`) and "
           f"proved by\n`tools/py/bbtools/symtm.py` (single steps by `rfl`, the `k` or `j` copies by `TM.cross_l` / "
           f"`TM.cross_r`).")
    return symtm.rules_file('Machine', ns, ['\n'.join(out)], doc)


if __name__ == '__main__':
    tm, at = sys.argv[1], float(sys.argv[2])
    print(lean_file(tm, at, ast.literal_eval(sys.argv[3]), ast.literal_eval(sys.argv[4]), sys.argv[5]), end='')
