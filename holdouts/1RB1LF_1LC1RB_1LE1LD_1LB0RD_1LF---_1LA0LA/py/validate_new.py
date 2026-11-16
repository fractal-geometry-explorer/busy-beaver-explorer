"""Check the rules added on 16 Nov 2026 (frozen words, cycle rules that emit a frozen word, nested-frame rules)
against the plain recursion:   python3 validate_new.py [random cases]

For each case the accelerated engine (all rules on) and the reference (frozen words, nested frames and jumps off:
the recursion G/h op by op, with the step constants of calibrate.py) compute op^q(T); the words and the step counts
must agree, and the words must also agree with Gref (the recursion on plain digit lists, no tokens)."""
import sys, random
sys.setrecursionlimit(1000000)
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import geng
from geng import *
geng.CST.update({'g0': 16, 'cend': -4, 'c1': 0, 'd1': 2, 'd0': 0, 'cR': 26})


def reset():
    for d in (geng.RULES, geng.NEG, geng.FULL, geng.RRULES, geng.RNEG, geng.NRULES, geng.NNEG, geng.FROZEN, geng.FPC):
        d.clear()


def run(name, q, ds, accel):
    reset()
    geng.ACCEL[0] = accel
    geng.FZ[0] = accel
    geng.NEST[0] = accel
    geng.C[0] = 0
    T = mk(ds)
    R, done = (gpow if name == 'G' else hpow)(q, T)
    return (None if R is None else to_digits(R)), done, geng.C[0]


def mk(ds):
    """a token list from digits, where an item ('P', n, w) stands for the run w^n (kept as one token)"""
    T = None
    for d in reversed(ds):
        T = econs(d[1], d[2], T) if type(d) is tuple else zcons(1, T) if d == 0 else dcons(d, T)
    return T


def ref_digits(name, q, ds):
    T = to_digits(mk(ds))
    for _ in range(q):
        T = Gref(T if name == 'G' else [0] + T)
        if T is None:
            return None
    return T


def check(label, name, q, ds, nd=None):
    if nd is not None:
        geng.NDEPTH[0] = nd
    a = run(name, q, ds, True)
    st = dict(geng.STATS)
    b = run(name, q, ds, False)
    geng.NDEPTH[0] = 200
    ok = a == b
    g = ref_digits(name, q, ds) if a[1] is True else 'skip'
    if g != 'skip':
        ok = ok and g == a[0]
    print("%-34s %s^%d, %d items: %s  (steps %d; jumps %d, nested %d, frozen %d)" % (
        label, name, q, len(ds), "equal" if ok else "DIFFERENT", a[2], st.get('jumps', 0), st.get('njumps', 0),
        st.get('frozen', 0)))
    return ok


def main():
    ok = True
    levels = ([1, 0] * 3 + [0, 0, 0, 0, 3]) * 12 + [0] * 7
    # an eater on fuel behind a frozen head: a cycle of 11 hits emits the frozen 20-digit rung
    for m in (40, 200):
        ds = [4, 0, 3, 0, 0, 0, 7, 0, 0, 0, 0, 3, ('P', m, (1, 0, 0))] + [0, 3, 3, 4, 0, 0, 0] + [1, 0] * 5 + levels
        ok &= check("eater, fuel %d" % m, 'h', 11 * (m // 3) - 5, ds)
    # G^12(12 0 (10030)^n X): the frame opens itself again at its 7th visit (machine 2, event 7)
    X = [1, 0, 0, 3, 0, 1, 0, 0, 3, 0] + [1, 0, 0] * 2 + [4, 3, 0] + [1, 0] * 30 + [3, 0, 0, 3, 1, 0, 4, 1, 0, 0, 3,
                                                                                     4, 3] + [1, 0] * 2 + levels
    for n in (30, 120, 400):
        ok &= check("nested G^12, n = %d" % n, 'G', 12, [2, ('P', n, (1, 0, 0, 3, 0))] + X, nd=3)
    # random words, some with long runs of a random short word
    rnd = random.Random(7)
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    bad = 0
    for i in range(N):
        ds = []
        while len(ds) < 60:
            if rnd.random() < 0.3:
                w = [rnd.choice([0, 0, 1, 3, 4]) for _ in range(rnd.randint(2, 6))]
                ds += w * rnd.randint(0, 3) + [('P', rnd.randint(3, 30), tuple(w))]
            else:
                ds.append(rnd.choice([0, 0, 0, 1, 1, 2, 3, 3, 4, 6, 7]))
        ds += levels
        r = check("random %d" % i, rnd.choice('Gh'), rnd.randint(1, 400), ds, nd=rnd.choice([3, 20, 200]))
        bad += not r
        ok &= r
    print("ALL EQUAL" if ok else "SOME DIFFER (%d random)" % bad)


main()
