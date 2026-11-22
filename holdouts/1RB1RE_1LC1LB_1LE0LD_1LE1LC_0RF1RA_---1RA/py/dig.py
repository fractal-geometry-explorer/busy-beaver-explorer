"""How deep can the parities of the 3/2 counter dig into the stack?  The real run against 2-adic counters.

A halt of 1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA needs the stack L of the epoch map to be used up completely
(README).  Measure the stack by its number of runs |L| and call the *dig* from epoch n the largest drop
|L_n| - |L_t| over the later epochs t >= n.  A halt from epoch n needs a dig of |L_n| from epoch n.

By lean/Adic.lean (`word_class`), the counters m that follow a parity word w from a stack L form one residue class
mod 2^|w|.  So for a 2-adic counter m drawn at random (Haar measure) the parities are fair independent coin flips,
and the measure of the counters that dig d runs from L is a probability we can estimate by flipping coins.

usage: python3 dig.py real N            the real run to epoch N (py/adic.py): how often the dig from an epoch
                                        reaches d runs, for each d
       python3 dig.py coins E T N SEED  N runs of T epochs with fair coin parities from the real stack at epoch E:
                                        the share of 2-adic counters whose dig from epoch E reaches d runs
       python3 dig.py along E1 E2 N T SEED  the same, each coin run from the real stack at a random epoch of
                                        [E1, E2): the 2-adic model of the frequencies `real` measures
       python3 dig.py short E DEPTH     every parity word of length <= DEPTH from the real stack at epoch E
                                        (stacks merged): the deepest dig a word of each length achieves, i.e.
                                        how many bits of the counter (mod 2^t) a dig of d runs pins at least
"""
import sys, os, random, collections, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import adic

TOP = 400          # entries of the real stack copied for the coin runs (the head never got near 400 deep)


def nruns(R): return sum(e[1] for e in R)


def stack_at(E):
    R, m, _ = adic.exact_start(adic.E0)
    if E > adic.E0:
        R, m, _, _ = adic.fast(E, R, m, adic.E0)
    return R


class Walker:
    """the top TOP entries of a stack; epochs with given parities, returning the change of the number of runs"""
    def __init__(self, R):
        self.R = [list(e) for e in R[-TOP:]]

    def step(self, p):
        stats = {'depth': collections.Counter(), 'K': collections.Counter()}
        adic.advance(self.R, p, stats, 1)
        if len(self.R) < 16: raise RuntimeError("dug near the bottom of the copy")
        return stats['drun']


def nruns_top(R):
    return sum(e[1] for e in R[-64:])     # only the top changes; differences are what count


def real(N):
    R, m, _ = adic.exact_start(adic.E0)
    series = [nruns(R)]; t0 = time.time()
    R, m, _, _ = adic.fast(N, R, m, adic.E0, series=series)
    assert series[-1] == nruns(R)
    # dig from each epoch: |L_n| - min_{t >= n} |L_t|
    n = len(series); mn = series[-1]; dig = [0] * n
    for i in range(n - 1, -1, -1):
        if series[i] < mn: mn = series[i]
        dig[i] = series[i] - mn
    half = n // 2                         # the epochs of the first half: their future is long enough to see
    cnt = collections.Counter(dig[:half])
    print("real run, epochs %d..%d (dig counted for the first half, %d epochs): |L| from %d to %d runs, %.0f s"
          % (adic.E0, N, half, series[0], series[-1], time.time() - t0))
    tail = half
    for d in range(0, max(cnt) + 1):
        print("  dig >= %2d runs: %d epochs (%.3e)" % (d, tail, tail / half))
        tail -= cnt.get(d, 0)
    steps = collections.Counter(series[i + 1] - series[i] for i in range(n - 1))
    print("change of |L| per epoch:", dict(sorted(steps.items())))


def coins(E, T, N, seed):
    R0 = stack_at(E)
    rng = random.Random(seed); cnt = collections.Counter(); t0 = time.time()
    for s in range(N):
        w = Walker(R0); h = 0; low = 0
        for t in range(T):
            h += w.step(rng.getrandbits(1))
            if h < low: low = h
        cnt[-low] += 1
    print("coin parities from the stack of epoch %d (%d runs): %d runs of %d epochs, %.0f s"
          % (E, nruns(R0), N, T, time.time() - t0))
    tail = N
    for d in range(0, max(cnt) + 1):
        print("  dig >= %2d runs: %d (%.3e)" % (d, tail, tail / N))
        tail -= cnt.get(d, 0)


def along(E1, E2, N, T, seed):
    """N coin runs of T epochs, each from the real stack at a random epoch of [E1, E2)"""
    rng = random.Random(seed)
    starts = sorted(rng.randrange(E1, E2) for _ in range(N))
    R, m, _ = adic.exact_start(adic.E0); ne = adic.E0
    cnt = collections.Counter(); t0 = time.time()
    for e in starts:
        if e > ne: R, m, _, _ = adic.fast(e, R, m, ne); ne = e
        w = Walker(R); h = 0; low = 0
        for t in range(T):
            h += w.step(rng.getrandbits(1))
            if h < low: low = h
        cnt[-low] += 1
    print("coin parities from the real stack at %d random epochs of [%d, %d): runs of %d epochs, %.0f s"
          % (N, E1, E2, T, time.time() - t0))
    tail = N
    for d in range(0, max(cnt) + 1):
        print("  dig >= %2d runs: %d (%.3e)" % (d, tail, tail / N))
        tail -= cnt.get(d, 0)


def short(E, DEPTH):
    R0 = stack_at(E)
    top = [list(e) for e in R0[-TOP:]]
    base = nruns_top(top)
    fr = {tuple(map(tuple, top)): 0}
    best = 0
    t0 = time.time()
    for t in range(1, DEPTH + 1):
        nf = {}
        for key, low in fr.items():
            for p in (0, 1):
                R = [list(e) for e in key]
                stats = {'depth': collections.Counter(), 'K': collections.Counter()}
                adic.advance(R, p, stats, 1)
                h = nruns_top(R) - base   # the top 64 entries hold every change (the cut never passed 32)
                k = tuple(map(tuple, R)); lo = min(low, h)
                if k not in nf or nf[k] > lo: nf[k] = lo
        fr = nf
        dug = -min(fr.values())
        print("words of length %2d: %7d stacks, deepest dig %d runs (%.0f s)" % (t, len(fr), dug, time.time() - t0),
              flush=True)


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[0] == 'real': real(int(float(a[1])))
    elif a[0] == 'along': along(int(float(a[1])), int(float(a[2])), int(a[3]), int(a[4]), int(a[5]))
    elif a[0] == 'coins': coins(int(float(a[1])), int(a[2]), int(a[3]), int(a[4]))
    else: short(int(float(a[1])), int(a[2]))
