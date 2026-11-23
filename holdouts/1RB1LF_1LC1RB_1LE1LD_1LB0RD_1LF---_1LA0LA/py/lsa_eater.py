"""symbolic super-cycle of an eater region: h^P(E[m] Omega) = Blk E[m - dm] h^c(Omega), m symbolic (a P(100) count)"""
import sys
from lsa_ladder import *
import geng
from geng import Lin, Rec, h, build_raw, build, to_tokens, Opaque, Budget, Event, show


def fuel_index(toks, start=0, thr=10 ** 6):
    for i in range(start, len(toks)):
        t = toks[i]
        if type(t) is tuple and t[0] == 'P' and t[1] > thr:
            return i
    return None


OPQ = [False]      # the last supercycle failed because the hits it passed down needed more of the rest


def supercycle(E, fi, Pmax=400, extra=0):
    """E: token list of the eater region (fuel at index fi), followed by an opaque rest.
    returns dict(P, dm, c, blk (tokens), cost (a, b) in m, nmin) or None"""
    OPQ[0] = False
    m0 = E[fi][1]
    m = Lin.var(0, m0)
    toks = list(E[:fi]) + [('P', m, E[fi][2])] + list(E[fi + 1:])
    T = build_raw(toks, (('O', 0), None))
    Rec.cons = []; Rec.work = 0; Rec.limit = 10 ** 7
    cs = geng.C[0]; geng.C[0] = 0
    res = None
    try:
        for P in range(1, Pmax + 1):
            T = h(T)
            out = to_tokens(T)
            if not (type(out[-1]) is tuple and out[-1][0] == 'O'):
                return None
            body = out[:-1]
            if len(body) < len(toks):
                continue
            k = len(body) - len(toks)
            tailb = body[k:]
            blk = body[:k]
            ok = True; dm = None
            for x, y in zip(tailb, toks):
                if type(y) is tuple and y[0] == 'P' and isinstance(y[1], Lin):
                    if not (type(x) is tuple and x[0] == 'P' and x[2] == y[2] and isinstance(x[1], Lin) and x[1].c == {0: 1}):
                        ok = False; break
                    dm = x[1].k
                elif x != y:
                    ok = False; break
            if not ok or dm is None or dm >= 0:
                continue
            if any(isinstance(t, Lin) or (type(t) is tuple and any(isinstance(z, Lin) for z in t)) for t in blk):
                continue
            # conditions: linear in m; need lower bound m >= mmin (all must be of the kind valid for large m)
            mmin = 0; okc = True
            for cf, kk, s, thr in Rec.cons:
                a = cf.get(0, 0)
                if a == 0:
                    if (s == 1 and kk < thr) or (s == -1 and kk > thr): okc = False
                    continue
                if (s == 1 and a < 0) or (s == -1 and a > 0):
                    okc = False; break
                nm = -((kk - thr) // a) if s == 1 else -((thr - kk) // (-a))
                mmin = max(mmin, nm)
            cost = geng.C[0]
            ab = (cost.c.get(0, 0), cost.k) if isinstance(cost, Lin) else (0, cost)
            if isinstance(cost, Lin) and set(cost.c) - {0}:
                okc = False
            if not okc:
                return None
            res = dict(P=P, dm=-dm, c=out[-1][1], blk=blk, cost=ab, mmin=mmin + (-dm))
            break
    except (Opaque, Budget, Event, RecursionError) as e:
        res = None
        OPQ[0] = isinstance(e, Opaque)
    finally:
        Rec.cons = None; geng.C[0] = cs
    return res


if __name__ == '__main__':
    import pickle
    d = pickle.load(open(sys.argv[1], 'rb')); toks = d['toks']
    levels, ib = segment(toks, 0, 'G')
    B = toks[ib:]
    fi = fuel_index(B)
    print('levels', len(levels), 'E region', show(build(B[:fi + 1], None))[:200], 'fuel digits', len(str(B[fi][1])))
    sc = supercycle(B[:fi + 1], fi)
    if sc:
        print({k: v for k, v in sc.items() if k != 'blk'}, 'block:', show(build(sc['blk'], None), 200))
