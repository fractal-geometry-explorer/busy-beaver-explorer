"""Counter tapes that halt: the shape of the tape alone does not prevent a halt.

The run from blank tape is, at every sweep start, `C> a^n0 s(d1) a^n1 ... s(dk) a^nk 01` (or one of a few irregular
patterns, see accel.py).  This script starts the machine from tapes of exactly that normal form but with other
block lengths (timers) and runs them with the exact accelerated simulator of accel.py.  Some of them halt, e.g.

    C> a^43 0101 a^4 0101 a^4 01        halts at step 4,905,443     (lean/Perturbed.lean, native_decide)

so a nonhalting proof has to use the values the blocks take in the actual run, not just the sweep rules and the
finitely many irregular patterns.

usage: python3 perturb.py small B N0      every tape with k <= 2 digits, blocks 1..B, n0 = 2..N0, to 10^40 steps
       python3 perturb.py random SEED T X T random tapes with 2..7 digits and block i below 4^(i+2), to 10^X steps
"""
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from accel import C, build, bulk, parse_norm, sweep  # noqa: E402

END = [['0', 1], ['1', 1]]


def run(tok, maxsteps, maxsweeps=10 ** 5):
    """Accelerated run from a sweep start: the halting step, or None if none within maxsteps."""
    steps = nf = 0
    while steps < maxsteps and nf < maxsweeps:
        p = parse_norm(tok)
        b = bulk(*p) if p else None
        if b:
            st, ds, t = b
            steps += ds
            tok = build(*st)
        else:
            try:
                tok, steps = sweep(tok, steps)
            except RuntimeError as e:
                return int(str(e).split()[-1])
            nf += 1
    return None


def tape(n0, d, blocks):
    return ''.join(w * n for w, n in build(n0, d, [b + C[x] for x, b in zip(d, blocks)], END))


def main():
    import itertools
    if sys.argv[1] == 'small':
        B, N0 = int(sys.argv[2]), int(sys.argv[3])
        found = []
        for k in (1, 2):
            for d in itertools.product(range(4), repeat=k):
                for bl in itertools.product(range(1, B + 1), repeat=k):
                    for n0 in range(2, N0 + 1):
                        h = run(build(n0, list(d), [b + C[x] for x, b in zip(d, bl)], END), 10 ** 40)
                        if h is not None:
                            found.append((h, n0, d, bl))
        found.sort()
        for h, n0, d, bl in found:
            print('halts at step %d: n0=%d digits=%s blocks=%s  %s' % (h, n0, d, bl, tape(n0, list(d), bl)))
        print('%d halting tapes' % len(found))
    else:
        seed, T, X = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        random.seed(seed)
        nh = 0
        for _ in range(T):
            k = random.randint(2, 7)
            d = [random.randrange(4) for _ in range(k)]
            bl = [random.randint(1, 4 ** (i + 2)) for i in range(k)]
            n0 = random.randint(2, 50)
            h = run(build(n0, d, [b + C[x] for x, b in zip(d, bl)], END), 10 ** X)
            if h is not None:
                nh += 1
                print('halts at a step with %d digits: n0=%d digits=%s blocks=%s' % (len(str(h)), n0, d, bl),
                      flush=True)
        print('%d of %d random tapes halt within 10^%d steps' % (nh, T, X))


if __name__ == '__main__':
    main()
