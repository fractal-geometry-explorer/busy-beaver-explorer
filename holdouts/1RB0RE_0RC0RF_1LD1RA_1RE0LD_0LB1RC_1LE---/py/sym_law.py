"""The rebuild law for every word, by a symbolic case analysis of the transient (py/sym_engine.py).

The transient after a rebuild is fed the counter's bits three at a time (lowest first).  Between two groups it stops
at a *frontier*: the pass machine in mid-sweep (phase A or C, k = 0) waiting on the open last gap of the zone, which is
then a single gap u in {0, 1, 2}.  Its list is a front of one or two entries and a history H of digits (blocks 3d + 2)
beyond them.  Ten shapes of frontier occur, each a family with at most two parameters (FAM below: phase, gap, the
front entry a and the second entry b, or 'D' when the second entry is already a digit of H).

  python3 py/sym_law.py cases        every shape and group value, every parameter value and every history:
                                     the next shape (or the end of the transient), all cases; the start from the
                                     rebuild state; the counter at the end; the shapes against the 7-state automaton
  python3 py/sym_law.py check N      N random rebuild states end to end with a concrete history, against
                                     py/rebuild_map.py (J, the list's time left and its length)
  python3 py/sym_law.py leaves N     every symbolic case against the same engine run concretely, N random parameter
                                     values and histories per shape and group value
"""
import os, sys, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sym_lin import *
import sym_lin
from sym_engine import *
from rebuild_map import AUTO

n, m, z, K = Lin.var('n'), Lin.var('m'), Lin.var('z'), Lin.var('k')
# the ten shapes: (phase, open gap, a mod 12, b mod 12 or 'D') -> (a, b) as affine forms
FAM = {("A", 0, 1, 3): (Lin(1), Lin(3)), ("A", 0, 2, 'D'): (2 + 12 * n, None), ("A", 1, 1, 'D'): (Lin(1), None),
       ("A", 1, 10, 'D'): (10 + 12 * n, None), ("A", 2, 6, 'D'): (6 + 12 * n, None),
       ("C", 0, 0, 7): (12 + 12 * n, 7 + 12 * m), ("C", 0, 1, 6): (1 + 12 * n, Lin(6)),
       ("C", 0, 4, 3): (4 + 12 * n, 3 + 12 * m), ("C", 0, 5, 'D'): (17 + 12 * n, None), ("C", 0, 8, 'D'): (8 + 12 * n, None)}
# the automaton state of each shape (C 0 4 3 with a = 4 is where the automaton stops)
STATE = {("C", 0, 1, 6): 'A', ("C", 0, 8, 'D'): 'B', ("A", 0, 1, 3): 'C', ("A", 0, 2, 'D'): 'C', ("A", 1, 1, 'D'): 'D',
         ("A", 1, 10, 'D'): 'E', ("C", 0, 0, 7): 'F', ("A", 2, 6, 'D'): 'G'}


def zoneOf(bs):
    zz = [3]
    for b in bs:
        if b: zz[-1] += 4
        else: zz.append(3)
    return zz


def frontier(t, v, hv=None, a=None, b=None):
    """the shape t fed the group v"""
    ph, u = t[0], t[1]
    if a is None: a, b = FAM[t]
    s = St(); s.mode = "ps"; s.ph = ph; s.k = Lin(0); s.hv = hv
    s.lb = [B(a)] + ([B(b)] if b is not None else []) + [('H', 0)]
    zz = zoneOf([bool((v >> i) & 1) for i in range(3)])
    s.us = [B(L(u) + zz[0] - 3)] + [B(x) for x in zz[1:]]
    return s


def shape(s):
    """the shape of a frontier, and its front entries"""
    lb = s.lb
    assert len(s.us) == 1 and s.us[0][0] == 'b' and s.us[0][1].isconst() and s.k == Lin(0)
    a = lb[0][1]; b = lb[1][1] if lb[1][0] == 'b' else None
    t = (s.ph, s.us[0][1].k, mod(a, 12), mod(b, 12) if b is not None else 'D')
    return t, a, b


def infam(t, a, b):
    """a, b in the family of shape t (for every value of the parameters)"""
    a0, b0 = FAM[t]
    def step12(x, x0):
        d = x - x0.k
        return d.k >= 0 and d.k % 12 == 0 and all(c > 0 and c % 12 == 0 for c in d.c.values())
    ok = (a == a0) if a0.isconst() else step12(a, a0)
    if b0 is None: return ok and b is None
    if b is None: return False
    return ok and ((b == b0) if b0.isconst() else step12(b, b0))


def name(t, a=None):
    if t == ("C", 0, 4, 3): return "stop" if a == Lin(0) + 4 else "C43+"
    if t == ("C", 0, 5, 'D'): return "C5D"
    return STATE[t]


def transitions(verbose=False):
    """every shape and group value: the cases, each checked to land in a family; the shape machine"""
    D = {}; ncases = 0; bad = []
    for t in FAM:
        for v in range(8):
            out = explore(frontier(t, v))
            srcs = ["stop", "C43+"] if t == ("C", 0, 4, 3) else [name(t)]
            res = {sname: set() for sname in srcs}
            for why, s, path in out:
                ncases += 1
                P = dict((x, e) for x, e in path if x == 'n')
                # which source (for C 0 4 3: a = 4 is n = 0)
                if t == ("C", 0, 4, 3) and 'n' in P:
                    mine = ["stop"] if P['n'] == Lin(0) else ["C43+"]
                else: mine = srcs
                if why == "end": dst = "end"
                elif why == "block":
                    t2, a2, b2 = shape(s)
                    if t2 not in FAM or not infam(t2, a2, b2): bad.append((t, v, t2, a2, b2)); continue
                    dst = name(t2, a2) if not (t2 == ("C", 0, 4, 3) and not a2.isconst()) else "C43+"
                else: bad.append((t, v, why)); continue
                for sn in mine: res[sn].add(dst)
            for sn in srcs:
                if len(res[sn]) != 1: bad.append((t, v, sn, res[sn])); continue
                D[(sn, v)] = res[sn].pop()
            if verbose: print(t, v, len(out), "cases", {sn: D.get((sn, v)) for sn in srcs}, flush=True)
    return D, ncases, bad


def bisim(D):
    """the greatest relation between shapes and automaton states that agrees on every group (entering 'stop' is the
    automaton's stop)"""
    S = sorted(set(STATE.values()) | {s for s, _ in D if s not in ("stop", "C43+", "C5D")})
    S = [s for s in S if s not in ("stop", "C43+", "C5D")]
    rel = {(x, y) for x in S for y in AUTO}
    ch = True
    while ch:
        ch = False
        for (x, y) in list(rel):
            for v in range(8):
                a = D[(x, v)]; b = AUTO[y][v]
                a = '.' if a == "stop" else a
                if (a == '.') != (b == '.') or (a != '.' and (a, b) not in rel):
                    rel.discard((x, y)); ch = True; break
    return {x: sorted(y for (xx, y) in rel if xx == x) for x in S}


def start_cases():
    """the rebuild state (a single block, the counter cz m r) to the first frontier: z zero groups, then v != 0;
    the list after the rebuild sub-round is 3 2^k (k digits 0; the far block 3 is never reached)"""
    out = {}
    for v in range(1, 8):
        bs = [bool((v >> i) & 1) for i in range(3)]
        tz = bs.index(True); Z0 = zoneOf(bs[tz + 1:])
        cases = [("t >= 1", 3 * z + tz)] if tz >= 1 else [("t = 0", None), ("t >= 1", 3 * (z + 1))]
        for nm, t in cases:
            s = St(); s.mode = "mom"; s.F = [R(2, K + 20), ('H', 0)]
            if t is None: s.l = Lin(4); s.us = [B(Z0[0] - 2)] + [B(x) for x in Z0[1:]]
            else: s.l = Lin(5); s.us = [B(4 * t - 4)] + [B(x) for x in Z0]
            res = set()
            for why, s2, path in explore(s):
                if why != "block": res.add(why); continue
                # the cases where the transient reaches past the k digits need k < 3z + c: not for k >= 3z + 14
                if any(c.c.get('k', 0) < 0 for c in s2.cons): continue
                assert not any(o[0] == 'pull' for o in s2.ops)
                t2, a2, b2 = shape(s2)
                res.add(name(t2, a2) if infam(t2, a2, b2) else ("out", t2))
            out[(v, nm)] = res
    return out


def czb_runs(runs):
    runs = [(b, c) for b, c in runs if not c == Lin(0)]
    t = Lin(0); i = 0
    while runs[i][0] == 0: t = t + runs[i][1]; i += 1
    b, c = runs[i]; rest = [(1, c - 1)] + runs[i + 1:]
    zz = [('b', Lin(3))]
    for b, c in rest:
        if c == Lin(0): continue
        if b == 1: zz[-1] = ('b', zz[-1][1] + 4 * c)
        else:
            if not c.isconst() or c.k > 1: zz.append(('r', Lin(3), c - 1))
            zz.append(('b', Lin(3)))
    return 4 * t + 1, zz


def norm(us):
    res = []
    for it in us:
        if it[0] == 'r' and it[2] == Lin(0): continue
        it = ('r', it[1], it[2]) if it[0] == 'r' else ('b', it[1])
        if res and it[1] == Lin(3) and res[-1][1] == Lin(3) and (it[0] == 'r' or res[-1][0] == 'r'):
            c1 = res[-1][2] if res[-1][0] == 'r' else Lin(1); c2 = it[2] if it[0] == 'r' else Lin(1)
            res[-1] = ('r', Lin(3), c1 + c2); continue
        res.append(it)
    return res


def end_cases():
    """the end of the transient: the counter is cz(m - 3J + 1, 2 (Y - 1)), Y = r / 8^J, on the bits read so far.
    After the stop the transient reads n zero groups and one more group v != 0 (from C 0 4 3, a = 4 + 12 n), or
    the group 1, n zero groups and v != 0 (from C 0 5 D, a = 17 + 12 n)"""
    tot = bad = 0
    for t in [("C", 0, 4, 3), ("C", 0, 5, 'D')]:
        for v in range(8):
            for why, s, p in explore(frontier(t, v)):
                if why != 'end': continue
                tot += 1; P = dict(p)
                if t == ("C", 0, 4, 3):
                    n0 = Lin(0) if P.get('n') == Lin(0) else (n + 1 if 'n' in P else n)
                    yb = [(1, 3 * n0)] + [(((v - 1) >> i) & 1, Lin(1)) for i in range(3)]     # Y - 1
                else:
                    yb = [(0, Lin(3)), (0, 3 * n)] + [((v >> i) & 1, Lin(1)) for i in range(3)]
                l, zz = czb_runs([(0, Lin(1))] + yb)                                            # 2 (Y - 1)
                if (s.l, norm(s.us)) != (l, norm(zz)): bad += 1; print("END DIFFERS", t, v, p)
    return tot, bad


# ---------------------------------------------------------------- concrete runs, against py/rebuild_map.py
def feed(s, v):
    zz = zoneOf([bool((v >> i) & 1) for i in range(3)])
    last = s.us[-1]; s.us = s.us[:-1] + [B(last[1] + zz[0] - 3)] + [B(x) for x in zz[1:]]; s.mode = "ps"


def run_concrete(k, rem, maxg=10 ** 6):
    """the transient of the rebuild state (k, ., rem) with a concrete list: (J, T, length of the list)"""
    j = 1
    while not (rem & ((1 << (3 * j)) - 1)): j += 1
    bs = [bool((rem >> i) & 1) for i in range(3 * j)]
    t = bs.index(True); Z0 = zoneOf(bs[t + 1:])
    s = St(); s.mode = "mom"; s.F = [R(2, k), ('H', 0)]; s.hv = 0
    if t >= 1: s.l = Lin(5); s.us = [B(4 * t - 4)] + [B(x) for x in Z0]
    else: s.l = Lin(4); s.us = [B(Z0[0] - 2)] + [B(x) for x in Z0[1:]]
    J = None
    while j <= maxg:
        out = explore(s, maxdepth=10 ** 7)
        assert len(out) == 1, out
        why, s, _ = out[0]
        if why == "end":
            Dd = s.F[:-1]
            return J, Tl(Dd) + (s.hv << sigl(Dd)), sigl(Dd) + s.hv.bit_length()
        assert why == "block", why
        if J is None and s.ph == "C" and s.lb[0][1] == Lin(4) and s.lb[1][0] == 'b' and s.lb[1][1].k % 12 == 3: J = j
        feed(s, (rem >> (3 * j)) & 7); j += 1
    return None


def main():
    cmd = sys.argv[1]
    if cmd == "cases":
        st = start_cases()
        print("start (z zero groups, then the group v):")
        for (v, nm), res in sorted(st.items()):
            want = AUTO['A'][v]
            got = sorted(res)
            ok = got == ["stop"] if want == '.' else (len(got) == 1 and got[0] in STATE.values() and got[0] == want)
            print(f"  v = {v} ({nm}): {got}, automaton {want}: {'ok' if ok else 'DIFFERS'}")
        D, nc, bad = transitions(verbose=True)
        print(f"{nc} cases over the 80 shape and group values; {len(bad)} outside the families or not deterministic")
        for b in bad: print("  ", b)
        print("the shape machine:")
        for sname in sorted(set(x for x, _ in D)): print("  ", sname, [D[(sname, v)] for v in range(8)])
        print("shapes against the automaton:", bisim(D))
        tot, eb = end_cases()
        print(f"end: {tot} cases, the counter differs from the law's in {eb}")
    elif cmd == "check":
        import rebuild_map as rm
        N = int(sys.argv[2]); random.seed(5); bad = 0; k = 200
        for _ in range(N):
            rem = random.randint(1 << 299, 1 << 300)
            J, T, sig = run_concrete(k, rem)
            J2, e, S = rm.local_word(rem)
            if not (J == J2 and T == (1 << (k + 4 * J - 1)) - 1 - e and sig == k + 4 * J - 1): bad += 1; print("DIFF", rem)
        print(f"{N} random rebuild states: J, T and the length of the list differ from py/rebuild_map.py in {bad}")
    elif cmd == "leaves":
        leaves(int(sys.argv[2]))


def leaves(N, seed=1):
    """each symbolic case, instantiated, against the engine run concretely (no case splits, no loops at once)"""
    random.seed(seed); bad = tried = 0
    for t in FAM:
        for v in range(8):
            out = explore(frontier(t, v)); a0, b0 = FAM[t]
            for _ in range(N):
                env0 = {'n': random.choice([0, 1, 2, random.randint(0, 12)]), 'm': random.choice([0, 1, random.randint(0, 8)])}
                if t == ("C", 0, 4, 3) and v == 1: pass
                h0 = random.randint(1 << 199, 1 << 200) << random.choice([0, 0, 1, 2, 5, 17])
                a, b = a0.ev(env0), (b0.ev(env0) if b0 is not None else None)
                c = explore(frontier(t, v, hv=h0, a=Lin(a), b=Lin(b) if b is not None else None), maxdepth=10 ** 7)
                assert len(c) == 1
                cw, cs, _ = c[0]
                hits = [inst(w, s, p, env0, h0, cw, cs) for w, s, p in out]
                hits = [x for x in hits if x is not None]
                tried += 1
                if hits != [True]: bad += 1; print("  DIFF", t, v, env0, hits)
    print(f"{tried} instances: the symbolic cases differ from the concrete run in {bad}")


def inst(w, s, path, env0, h0, cw, cs):
    """None if the case does not apply to these values, else whether it gives the concrete result"""
    env = dict(env0)
    for v, ex in path:
        if v not in ('n', 'm'): continue
        if ex.isconst():
            if env[v] != ex.k: return None
            env[v] = None
        else:
            q, r = ex.c[v], ex.k
            if env[v] is None or env[v] < r or (env[v] - r) % q: return None
            env[v] = (env[v] - r) // q
    env = {x: y for x, y in env.items() if y is not None}
    h = h0
    for op in s.ops:
        if op[0] == 'pull':
            if h <= 0: return None
            x = (h & -h).bit_length() - 1; ex = op[3]
            unk = [u for u in ex.c if u not in env]
            if unk:
                u = unk[0]; cc = ex.c[u]; rest = ex.k + sum(c2 * env[u2] for u2, c2 in ex.c.items() if u2 != u)
                if (x - rest) % cc or (x - rest) // cc < 0: return None
                env[u] = (x - rest) // cc
            elif ex.ev(env) != x: return None
            h = (h >> x) >> 1
        elif op[0] == 'dbl': h <<= op[3].ev(env)
        elif op[0] == 'add':
            e = op[4].ev(env)
            if e < 0: return None
            h += op[3] * (1 << e)
            if h < 0: return None
        elif op[0] == 'push':
            Dd = [(it[0], Lin(it[1].ev(env))) + ((Lin(it[2].ev(env)),) if it[0] == 'r' else ()) for it in op[3]]
            h = Tl(Dd) + (h << sigl(Dd))
    if any(c.ev(env) < 0 for c in s.cons): return None
    if w != cw: return False
    if w == "end":
        Dd = [(it[0], Lin(it[1].ev(env))) + ((Lin(it[2].ev(env)),) if it[0] == 'r' else ()) for it in s.F[:-1]]
        Dc = cs.F[:-1]
        return (Tl(Dd) + (h << sigl(Dd)) == Tl(Dc) + (cs.hv << sigl(Dc)) and s.l.ev(env) == cs.l.k
                and [x[1].ev(env) for x in s.us] == [x[1].k for x in cs.us])
    pre = [x[1].ev(env) for x in s.lb[:-1]]
    return (pre == [x[1].k for x in cs.lb[:-1]] and s.ph == cs.ph and h == cs.hv
            and [x[1].ev(env) for x in s.us] == [x[1].k for x in cs.us])


if __name__ == "__main__":
    main()
