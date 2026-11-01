"""How the top blocks decide halting: statistics of d1 at the returns to the left end, and the odds of a halt.

usage:
  python3 top_stats.py odds                 the next return's lower bound and the odds of a future halt, from
                                            runs/superrun_long.txt
  python3 top_stats.py toppass MAX_S        on the orbit from blank tape (to super step MAX_S, by the tables of
                                            superrun.py): how often a wave that reaches the k-th block from the left
                                            passes it, for k = 1, 2, ...  (1e17: about 30 s)
  python3 top_stats.py ensemble FILE...     the returns in output files of c/ensemble.c: the halting law, v2(d1), the
                                            odd part u mod 2^t, d1 mod q, the leading bits, and the near-halts
  python3 top_stats.py fast FILE...         the totals that c/ensemble_fast.c prints (summed over the files): the
                                            halting law and v2(d1) = s against the random model, by the size of d1

At a return the wave has passed all m blocks with d even, N = 2^(m-1) d1, and the machine halts iff d1 is a power of
two (lean/Wave.lean).  Write d1 = 2^s u with u odd.  The random model says d1 is a power of two with probability
1/(d1 ln 2): that is what `ensemble` tests on the map from random starts, at every scale it can reach, through the
near-halts (u < 2^c, expected (2^c / 2) / (d1 ln 2) per return), which are halts for c = 1.  lean/Monotone.lean proves
that N increases at every super step; between returns m is fixed, so the next d1 exceeds the current N / 2^(m-1),
which is at least p_1 + p_2/2 + p_3/4 + p_4/8 for the four top blocks that c/superrun.c prints (`odds`).
"""
import math
import os
import random
import sys
from collections import Counter, defaultdict
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from superrun import periodic_table, ADD, WAVE  # noqa: E402

LN2 = math.log(2)
LONG = os.path.join(HERE, "..", "runs", "superrun_long.txt")


def v2(x):
    return (x & -x).bit_length() - 1


def odds(path=LONG, trials=20000, seed=1):
    """The returns of the long run, the next return's lower bound, and the future sum of 1/(d1 ln 2)."""
    d1s, top = [], None
    for line in open(path):
        f = line.split()
        if f and f[0] == "left":
            d1s.append(int(dict(zip(f[1::2], f[2::2]))["d1"]))
        elif f and f[0] == "status" and "top" in f:
            top = [int(x) for x in f[f.index("top") + 1:]]
    print(f"returns: {len(d1s)}; the last d1 = {d1s[-1]} ({d1s[-1]:.3e}, {d1s[-1].bit_length()} bits, "
          f"log2 {math.log2(d1s[-1]):.2f}, s = {v2(d1s[-1])})")
    lb = sum(Fraction(p, 2 ** i) for i, p in enumerate(top))
    print(f"top blocks at the end of the run: {top}")
    print(f"the next return has d1 > p1 + p2/2 + p3/4 + p4/8 = {float(lb):.4e} = 2^{math.log2(lb):.2f}, so it halts "
          f"only if d1 = 2^a with a >= {math.ceil(math.log2(lb))}, i.e. 2^{math.ceil(math.log2(lb))} | d1")
    lg = [math.log2(d) for d in d1s]
    inc = [b - a for a, b in zip(lg, lg[1:])]
    late = inc[5:]                                    # from the sixth return on (d1 > 10^5)
    print(f"growth of log2 d1 per return: {sum(inc) / len(inc):.2f} over all, {sum(late) / len(late):.2f} from the "
          f"sixth return on")
    rng = random.Random(seed)
    sums = []
    floor = math.log2(lb)
    for _ in range(trials):
        x, tot = lg[-1], 0.0
        for k in range(1000):
            x += rng.choice(late)
            if k == 0:
                x = max(x, floor)
            tot += 2 ** -x / LN2
            if x > lg[-1] + 200:
                break
        sums.append(tot)
    sums.sort()
    q = lambda f: sums[int(f * (len(sums) - 1))]  # noqa: E731
    print(f"future sum of 1/(d1 ln 2), resampling those increments ({trials} paths): median {q(0.5):.1e}, "
          f"10% {q(0.1):.1e}, 90% {q(0.9):.1e}, mean {sum(sums) / len(sums):.1e}")
    print(f"2-adic part alone: the next return needs v2(d1) >= {math.ceil(floor)}, "
          f"chance 2^-{math.ceil(floor)} = {2 ** -math.ceil(floor):.1e} if v2(d1) is geometric")


def toppass(max_s, depth=24, after=10 ** 6):
    """reach[k], pass[k]: waves that reach the k-th block from the left (k = 0 the top block) after super step
    `after`, and how many of them have d even there (pass on; at the top, d1 even)."""
    reach, pas = [0] * depth, [0] * depth
    tab, tail, K = [(1, WAVE, 10, 0)], (0, 0), 0
    up, S, seen, wraps = [6, 1], 0, {}, 0
    while True:
        for dt, typ, v, _ in tab:
            S += dt
            if typ == ADD:
                up[0] += v
            else:
                h, k = v, 0
                while True:
                    d = up[k] + h
                    t = len(up) - 1 - k
                    if t < depth and S > after:
                        reach[t] += 1
                        pas[t] += d % 2 == 0
                    if k == len(up) - 1:
                        s, u = v2(d), d >> v2(d)
                        if u == 1:
                            raise RuntimeError(f"halt at super step {S}")
                        del up[-1]
                        up += [u << q for q in range(s - 1, -1, -1)] + [(u + 5) // 2, (u - 1) // 2]
                        break
                    if d % 2:
                        up[k], up[k + 1] = (d + 5) // 2, up[k + 1] + (d - 1) // 2
                        break
                    up[k] = h = d // 2
                    k += 1
            if S >= max_s:
                return reach, pas
        S += tail[0]
        wraps += 1
        if len(up) < 3:
            continue
        if up[0] in seen:
            new = periodic_table(tab, tail, up[0], wraps - seen[up[0]])
            if new:
                tab, tail = new
                K += 1
                up = up[1:]
                seen, wraps = {}, 0
                continue
        seen[up[0]] = wraps


def read_ensemble(files):
    norb, rets = 0, []
    for fn in files:
        for line in open(fn):
            f = line.split()
            if f and f[0] == "start":
                norb += 1
            elif f and f[0] == "R" and len(f) == 6:
                rets.append((int(f[4]), int(f[5])))
    return norb, rets


def ensemble(files):
    norb, rets = read_ensemble(files)
    print(f"orbits {norb}, returns {len(rets)}, halts {sum(h for _, h in rets)}")
    print("\nThe halting law: halts against the sum of 1/(d1 ln 2), by the size of d1")
    bins = defaultdict(lambda: [0, 0, 0.0])
    for d, h in rets:
        b = bins[d.bit_length() - 1]
        b[0] += 1
        b[1] += h
        b[2] += 1 / (d * LN2)
    print(" log2 d1   returns  halts  expected  ratio")
    for b in sorted(bins):
        n, h, e = bins[b]
        if e > 0.005:
            print(f"   {b:3d}  {n:9d}  {h:5d}  {e:8.2f}  {h / e:5.2f}")
    for lo in (3, 6):
        h = sum(v[1] for k, v in bins.items() if k >= lo)
        e = sum(v[2] for k, v in bins.items() if k >= lo)
        print(f"  d1 >= 2^{lo}: {h} halts, {e:.1f} expected, ratio {h / e:.3f} +- {math.sqrt(e) / e:.3f}")

    print("\nv2(d1) = s at the returns: P(s >= t) * 2^t, by the size of d1 (1 = geometric)")
    for a, b in ((12, 16), (16, 20), (20, 24), (24, 40)):
        ss = [v2(d) for d, _ in rets if a <= d.bit_length() - 1 < b]
        c, tail, row = Counter(ss), len(ss), []
        for t in range(14):
            row.append(f"{tail * 2 ** t / len(ss):.2f}")
            tail -= c[t]
        print(f"  d1 in [2^{a}, 2^{b}) ({len(ss)} returns): " + " ".join(row))

    big = [d for d, _ in rets if d >= 1 << 12]
    print(f"\nResidues at the {len(big)} returns with d1 >= 2^12 (returns of one orbit are not independent)")
    for t in (2, 3, 4, 6, 8):
        c = Counter((d >> v2(d)) % (1 << t) for d in big)
        vals = [c[r] for r in range(1, 1 << t, 2)]
        e = len(big) / len(vals)
        chi = sum((x - e) ** 2 / e for x in vals)
        print(f"  u mod 2^{t}: chi2 {chi:6.1f} on {len(vals) - 1} dof; u = 1 mod 2^{t}: {c[1] / e:.3f} of uniform")
    for q in (3, 5, 7, 9, 11, 13, 17, 31):
        c = Counter(d % q for d in big)
        e = len(big) / q
        p2 = {pow(2, a, q) for a in range(1, 200)}
        chi = sum((c[r] - e) ** 2 / e for r in range(q))
        mass = sum(c[r] for r in p2) / (e * len(p2))
        print(f"  d1 mod {q:2d}: chi2 {chi:6.1f} on {q - 1:2d} dof; the residues of powers of two get {mass:.3f} of "
              f"their share")
    fr = [math.log2(d) % 1 for d in big]
    h = Counter(int(x * 10) for x in fr)
    print("  leading bits, frac(log2 d1) in tenths (1 = uniform): " +
          " ".join(f"{h[i] * 10 / len(fr):.2f}" for i in range(10)))
    near = sum(1 for x in fr if x < 0.01 or x > 0.99) / len(fr)
    print(f"  within 0.01 of a power of two: {near:.4f} (uniform 0.02)")

    print("\nNear-halts: returns with u < 2^c, against (2^c / 2) / (d1 ln 2) each (c = 1 is the halt);"
          " only returns with d1 >= 2^(c+6)")
    bands = ((8, 12), (12, 16), (16, 20), (20, 24), (24, 40))
    print("   c  " + "  ".join(f"[2^{a},2^{b})".center(19) for a, b in bands) + "   all")
    for c in range(1, 21):
        U, row, to, te = 1 << c, [], 0, 0.0
        for a, b in bands:
            o, e = 0, 0.0
            for d, _ in rets:
                if a <= d.bit_length() - 1 < b and d >= U << 6:
                    o += (d >> v2(d)) < U
                    e += (U / 2) / (d * LN2)
            to, te = to + o, te + e
            row.append(f"{o:5d}/{e:7.1f} {o / e:4.2f}" if e >= 1 else " " * 19)
        print(f"  {c:2d}  " + "  ".join(row) + (f"   {to}/{te:.1f} = {to / te:.3f}" if te else ""))


def read_fast(files):
    """Adds up the totals of c/ensemble_fast.c: orbits, dropped, returns, halts, cell[b][s], inv[b], pair[a][c],
    rcell[k][b][s]."""
    tot = Counter()
    cell, inv, pair, rcell = Counter(), defaultdict(float), Counter(), Counter()
    for fn in files:
        for line in open(fn):
            f = line.split()
            if not f:
                continue
            if f[0] == "orbits":
                for k, v in zip(f[0::2], f[1::2]):
                    tot[k] += int(v)
            elif f[0] == "cell":
                cell[int(f[1]), int(f[2])] += int(f[3])
            elif f[0] == "inv":
                inv[int(f[1])] += float(f[2])
            elif f[0] == "pair":
                pair[int(f[1]), int(f[2])] += int(f[3])
            elif f[0] == "rcell":
                rcell[int(f[1]), int(f[2]), int(f[3])] += int(f[4])
    return tot, cell, inv, pair, rcell


def p_div(b, t):
    """P(2^t | d) for d of b bits (2^(b-1) <= d < 2^b) with the density 1/(d ln 2) of the random model (leading bits
    uniform in log): the sum of 1/(k 2^t ln 2) over the multiples k 2^t in the range.  2^-t when t << b."""
    if t >= b:
        return 0.0
    lo, hi = -(-(1 << (b - 1)) >> t), ((1 << b) - 1) >> t
    if hi - lo > 10 ** 5:
        return 2.0 ** -t
    return sum(1 / k for k in range(lo, hi + 1)) / (2 ** t * LN2)


def fast(files, tmax=24):
    tot, cell, inv, pair, rcell = read_fast(files)
    nb = Counter()
    for (b, s), n in cell.items():
        nb[b] += n
    print(f"orbits {tot['orbits']} (dropped {tot['dropped']}), returns {tot['returns']}, halts {tot['halts']}")

    print("\nThe halting law: halts against the sum of 1/(d1 ln 2), by the size of d1 (b bits: 2^(b-1) <= d1 < 2^b)")
    print("    b      returns   halts   expected  ratio")
    for b in sorted(nb):
        h, e = cell[b, b - 1], inv[b] / LN2
        if e > 0.005:
            print(f"  {b:3d}  {nb[b]:11d}  {h:6d}  {e:9.2f}  {h / e:5.2f}")
    for lo in (4, 7, 13, 17):
        h = sum(cell[b, b - 1] for b in nb if b >= lo)
        e = sum(inv[b] for b in nb if b >= lo) / LN2
        if e > 0:
            print(f"  d1 >= 2^{lo - 1}: {h} halts, {e:.1f} expected, ratio {h / e:.3f} +- {math.sqrt(e) / e:.3f}")

    def tail(b, t):
        return sum(n for (bb, s), n in cell.items() if bb == b and s >= t)

    print("\nv2(d1) = s at the returns: observed / expected for s >= t (expected: P(2^t | d1) for d1 of b bits with "
          "density 1/(d1 ln 2), `p_div`), by the size of d1; in brackets (observed - expected) / sqrt(expected)")
    bands = ((12, 16), (16, 20), (20, 24), (24, 28), (28, 40), (40, 128))
    for a, z in bands:
        bs = [b for b in nb if a < b <= z]
        n = sum(nb[b] for b in bs)
        if not n:
            continue
        row = []
        for t in range(4, tmax + 1):
            o = sum(tail(b, t) for b in bs)
            e = sum(nb[b] * p_div(b, t) for b in bs)
            if e >= 3:
                row.append(f"t={t} {o / e:.3f} ({(o - e) / math.sqrt(e):+.1f})")
        print(f"  d1 in [2^{a}, 2^{z}) ({n} returns): " + "; ".join(row))
    print("  pooled over d1 >= 2^16, only returns with b >= t + 6 (the multiples of 2^t in the range at least 32):")
    for t in range(4, tmax + 1):
        bs = [b for b in nb if b > 16 and b >= t + 6]
        o = sum(tail(b, t) for b in bs)
        e = sum(nb[b] * p_div(b, t) for b in bs)
        if e >= 3:
            print(f"    t = {t:2d}: {o:9d} observed, {e:11.1f} expected, ratio {o / e:.4f} +- {math.sqrt(e) / e:.4f}"
                  f"  ({(o - e) / math.sqrt(e):+.1f} sigma)")

    print("\nBy the odd part instead: returns with u < 2^c (u = d1 / 2^s, so s >= b - c), observed / expected "
          "(expected `p_div`(b, b - c) per return; c = 1 is the halt); only b >= c + 7")
    for c in range(1, 21):
        row, to, te = [], 0, 0.0
        for a, z in bands:
            bs = [b for b in nb if a < b <= z and b >= c + 7]
            o = sum(tail(b, b - c) for b in bs)
            e = sum(nb[b] * p_div(b, b - c) for b in bs)
            to, te = to + o, te + e
            row.append(f"{o:6d}/{e:8.1f} {o / e:4.2f}" if e >= 1 else " " * 20)
        pooled = f"   {to}/{te:.1f} = {to / te:.3f} ({(to - te) / math.sqrt(te):+.1f})" if te else ""
        print(f"  {c:2d}  " + "  ".join(row) + pooled)

    if rcell:
        print("\nBy the return's number k in its orbit (1 = the first return): observed / expected for s >= t over the "
              "returns with d1 >= 2^16 and b >= t + 6, and the mean log2 d1 of those returns")
        ks = sorted({k for k, _, _ in rcell})
        for k in ks:
            nk = Counter()
            for (kk, b, ss), n in rcell.items():
                if kk == k:
                    nk[b] += n
            tot_k = sum(n for b, n in nk.items() if b > 16)
            if tot_k < 1000:
                continue
            mean_b = sum((b - 0.5) * n for b, n in nk.items() if b > 16) / tot_k
            row = []
            for t in (4, 6, 8, 10, 12, 14):
                bs = [b for b in nk if b > 16 and b >= t + 6]
                o = sum(n for (kk, b, ss), n in rcell.items() if kk == k and b in bs and ss >= t)
                e = sum(nk[b] * p_div(b, t) for b in bs)
                if e >= 10:
                    row.append(f"t={t} {o / e:.3f} ({(o - e) / math.sqrt(e):+.1f})")
            print(f"  k = {k:2d} ({tot_k} returns, log2 d1 about {mean_b:.1f}): " + "; ".join(row))

    print("\nConsecutive returns of an orbit (both d1 >= 2^12): P(next s >= t | this s >= a) * 2^t")
    for a in (0, 2, 4, 6):
        base = sum(n for (x, y), n in pair.items() if x >= a)
        row = []
        for t in (2, 4, 6, 8):
            o = sum(n for (x, y), n in pair.items() if x >= a and y >= t)
            row.append(f"t={t} {o * 2 ** t / base:.3f}" if base else "")
        print(f"  this s >= {a} ({base} pairs): " + "  ".join(row))


def main(argv):
    if argv[:1] == ["odds"]:
        odds()
    elif argv[:1] == ["toppass"] and len(argv) > 1:
        reach, pas = toppass(float(argv[1]))
        print("k (from the left)  waves reaching it  d even (pass on)  fraction")
        for k, (r, p) in enumerate(zip(reach, pas)):
            if r:
                print(f"{k + 1:4d}  {r:12d}  {p:12d}  {p / r:.4f}")
    elif argv[:1] == ["ensemble"] and len(argv) > 1:
        ensemble(argv[1:])
    elif argv[:1] == ["fast"] and len(argv) > 1:
        fast(argv[1:])
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
