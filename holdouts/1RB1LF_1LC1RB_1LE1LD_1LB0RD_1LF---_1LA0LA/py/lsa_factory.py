"""The factory rule behind the x64 eater, checked with symbolic counts:  python3 lsa_factory.py

Below an eater of 1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA (phase 6 of the run from wall visit 10^3200, and
most phases after it) the rest of the word starts with the factory

    (10) 4 0^6 (10) 4 0^4 3 [100]^M 3 4 0^3 4 3 4 0^3 (10) X

Each hit passed down by the eater goes to it.  The factory writes rungs w = 40001010431040300010 in front of
itself, so after a few hits it reads (10) w^n 4 0^6 ...  For each of the 11 states of its cycle (after 11000 + r
hits, r = 0..10) this script makes n and M symbolic (geng.Lin) and runs 11 more hits, recording every
comparison the recursion makes.  From all 11 states the result is the same state with one more rung (written
out right after w^n), M - 6 for M, and 2 more hits on the rest X:

    h^11(state(n, M) X) = state(n + 1, M - 6) h^2(X)     for every n >= 1 and every M above the recorded bound.

So 11 hits make one rung of the next eater's fuel: with the 21 hits of an eater super-cycle that is law A,
11 F' = 21 K + e (lean/Factory.lean of 1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA derives it from this rule).
"""
import sys, os
sys.set_int_max_str_digits(0)
sys.setrecursionlimit(1000000)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import geng, lsa_phase
from geng import Lin, Rec

RUNG = (4, 0, 0, 0, 1, 0, 1, 0, 4, 3, 1, 0, 4, 0, 3, 0, 0, 0, 1, 0)
FAC = [('R', 1), 4, ('Z', 6), ('R', 1), 4, ('Z', 4), 3]
AFT = [3, 4, ('Z', 3), 4, 3, 4, ('Z', 3), ('R', 1)]
M0 = 10 ** 6


def state(q):
    """the factory after q hits (concrete), as folded tokens without the rest"""
    T = geng.build(FAC + [('P', M0, (1, 0, 0))] + AFT, (('O', 0), None))
    W, _ = geng.hpow(q, T)
    t = lsa_phase.fold_toks(geng.to_tokens(W))
    return t[:-1], t[-1][1]


def digits(ts):
    return sum([lsa_phase._tok_digits(t) for t in ts], [])


def conc(ts):
    return lsa_phase.fold_toks([('P', t[1].v, t[2]) if type(t) is tuple and t[0] == 'P' and isinstance(t[1], Lin)
                                else t for t in ts])


def check(r):
    a, _ = state(11 * 1000 + r)
    ir = [i for i, t in enumerate(a) if type(t) is tuple and t[0] == 'P' and t[2] == RUNG]
    assert len(ir) == 1, 'rung run not found'
    ir = ir[0]
    iM = max([i for i, t in enumerate(a) if type(t) is tuple and t[0] == 'P' and t[2] == (1, 0, 0)],
             key=lambda i: a[i][1])
    st = list(a)
    st[ir] = ('P', Lin.var(0, a[ir][1]), RUNG)
    st[iM] = ('P', Lin.var(1, a[iM][1]), (1, 0, 0))
    T = geng.build_raw(st, (('O', 0), None))
    Rec.cons = []; Rec.work = 0; Rec.limit = 10 ** 7
    try:
        for _ in range(11):
            T = geng.h(T)
        out = geng.to_tokens(T)
    finally:
        cons = Rec.cons; Rec.cons = None
    b = conc(out[:-1]); a = conc(st)
    want_tail = [('P', t[1] - 6, t[2]) if j == iM else t for j, t in enumerate(a)][ir + 1:]
    ok = any(b[:ir + 1] == a[:ir + 1] and digits(b[ir + 1:ir + 1 + k]) == list(RUNG) and b[ir + 1 + k:] == want_tail
             for k in range(1, 12))
    # the recorded conditions: only lower bounds on n (var 0) and M (var 1)
    nlo = max([(thr - c) for co, c, s, thr in cons if co == {0: 1}], default=0)
    mlo = max([(thr - c) for co, c, s, thr in cons if co == {1: 1}], default=0)
    simple = all(set(co) <= {0, 1} and len(co) == 1 and list(co.values()) == [1] and s == 1 for co, c, s, thr in cons)
    return ok and out[-1] == ('O', 2) and simple, len(cons), nlo, mlo


def main():
    allok = True
    for r in range(11):
        ok, nc, nlo, mlo = check(r)
        allok &= ok
        print('state r = %2d: rule %s  (%d conditions: n >= %d, M >= %d)' % (r, 'holds' if ok else 'FAILS', nc, nlo, mlo))
    print('h^11: n -> n + 1, M -> M - 6, 2 hits down, from all 11 states' if allok else 'NOT VERIFIED')
    sys.exit(0 if allok else 1)


if __name__ == '__main__':
    main()
