"""Single-stretch exclusion for every route prefix found by routetree.py, in both loop phases.
usage: routeexclude2.py routes.jsonl kmin kmax candidates_out summary_out [slack]
A halt at width E in [2^k, 2^(k+1)) needs H + 4p + 8 >= k - slack + 9 meetings' worth of halvings: with x = d + 2,
each meeting at most halves x, the loop divides R = W - c - 1 by 16 per pass, and a halt needs x <= 4, so
4p >= k - H - 10 exactly; slack 12 leaves two more halvings of margin.  The lock (64^p <= |L1| <= 280E) then caps
k at 3H + 3*slack + 18.26."""
import sys, json, math
from fractions import Fraction as F
from conc import Model, Pos
import routeexclude as RX

def halvings(shapes, outs, m_ex, E_ex):
    md, err = RX.forced(m_ex, E_ex, shapes, outs, 0, F(2) ** 80)
    if md is None: return None
    mk = md.marks(); d = md.W - mk[-1][1]
    a, b = d.f[0], d.f[1]
    lo = min(b, a + b)
    if lo <= 0: return float('inf')
    return math.log2(1 / float(lo))

if __name__ == '__main__':
    routes = [json.loads(l) for l in open(sys.argv[1])]
    kmin, kmax = int(sys.argv[2]), int(sys.argv[3])
    cand = open(sys.argv[4], 'w'); summ = open(sys.argv[5], 'w')
    E_ex = 2 ** 40 + 1
    S = int(sys.argv[6]) if len(sys.argv) > 6 else 12
    for idx, r in enumerate(routes):
        m_ex = int(E_ex * r['ratio']) // 2 * 2
        for phase in ('A', 'B'):
            shapes = list(r['shapes']); outs = list(r['outs'])
            if phase == 'B': shapes += ['GBW', 'GWWW']; outs += [2, 2, 2]
            H = halvings(shapes, outs, m_ex, E_ex)
            if H is None: summ.write(f"{idx} {phase} prefix geometry fails\n"); continue
            if H == float('inf'): summ.write(f"{idx} {phase} UNBOUNDED route halvings\n"); continue
            kcap = min(kmax, int(3 * H + 3 * S + 18.26) + 1)
            cache = {}; total = 0; status = []
            for k in range(kmin, kcap + 1):
                p = max(1, math.ceil((k - S - H) / 4))
                if p not in cache:
                    md, err = RX.forced(m_ex, E_ex, shapes, outs, p, F(2) ** (4 * p + 100))
                    if md is None: cache[p] = None
                    else: cache[p] = RX.coset_of(md)
                C = cache[p]
                if C is None: continue
                cnt = 0
                for m, E in RX.points(C, k):
                    cand.write(f"{m} {E}\n"); total += 1; cnt += 1
                    if cnt > 20_000_000: status.append(f"k={k} TRUNCATED"); break
            ok = [p for p, C in cache.items() if C is not None]
            summ.write(f"{idx} {phase} H={H:.2f} kmax={kcap} consistent_p={sorted(ok)} candidates={total} {' '.join(status)} measure={r['measure']:.3e} {' '.join(shapes)}\n")
            summ.flush(); cand.flush()
    print("done")
