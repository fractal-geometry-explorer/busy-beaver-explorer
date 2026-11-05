"""Does the macro machine stay unstuck because of its exact values, or only because of the parities?

Take configurations of the two-stack form (py/twostack.py) from the run from blank, change a few even numbers by 2
(a value of L or R, or an even gap of at least 2; every parity stays the same), and run on.  The run itself never
gets stuck; if the perturbed ones do, then whatever keeps the run unstuck depends on its exact values, and no closed
family that only constrains parities (plus anything the perturbation keeps) can exist.

usage:
  python3 py/perturb.py T H [SEED] [K]   snapshots every T/200 steps of the first T, 5 perturbations of each with K
                                         changes (default 3), each run H steps; prints the stuck ones (snapshot time,
                                         steps to stuck) and the totals
  python3 py/perturb.py example          one changed entry: the run goes on, the changed configuration gets stuck
"""
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from callstack import start  # noqa: E402
from twostack import END, cursor, norm, show, zstep  # noqa: E402


def snapshots(T, n=200):
    z, out = start(), []
    for t in range(T):
        if t > 10000 and t % (T // n) == 0:
            out.append((t, [list(e) for e in z]))
        z = zstep(z)
    return out


def perturb(z, k, rng):
    z = [list(e) for e in z]
    c = cursor(z)
    changes = []
    for _ in range(k):
        j = rng.randrange(len(z))
        d = rng.choice((-2, 2))
        if rng.random() < 0.5 or z[j][1] in (END, 0):
            # a frame of R has value a + 2 >= 2 until it is flipped; keep it so, and keep L entries >= 0
            if z[j][0] % 2 == 0 and z[j][0] + d >= (2 if j >= c else 0):
                z[j][0] += d
                changes.append((j, "value", d))
        elif z[j][1] % 2 == 0 and z[j][1] + d >= 2:
            z[j][1] += d
            changes.append((j, "gap", d))
    return norm(z), changes


def run(z, H):
    """Steps until stuck (None if not within H) and the number of R2 steps on the way."""
    r2 = 0
    for t in range(H):
        if z[cursor(z)][1] == -1:
            r2 += 1
        z = zstep(z)
        if z is None:
            return t + 1, r2
    return None, r2


# The run's configuration after 90,000 steps of the two-stack form, with one entry of L changed from 0 to 2 (the 7th
# from the bottom).  The run itself goes on; this one gets stuck after 24,141 steps.
EXAMPLE_AT = 90000
EXAMPLE = [[0, 0], [0, 0], [0, 0], [6, 0], [2, 0], [0, 0], [2, 0], [0, 0], [0, 0], [2, 2], [2, 2], [4, 0], [4, 4],
           [4, 8], [2, 2], [2, 0], [2, 0], [4, 2], [4, 4], [2, 2], [2, 2], [12, 0], [5, 1], [8, 0], [1, END]]


def main(argv):
    if argv[0] == "example":
        z = start()
        for _ in range(EXAMPLE_AT):
            z = zstep(z)
        e = norm([list(x) for x in EXAMPLE])
        print("run after", EXAMPLE_AT, "steps:", show(z))
        print("perturbed:              ", show(e))
        for name, c in (("run", z), ("perturbed", e)):
            n, r2 = run(c, 10 ** 5)
            print(f"{name}: " + (f"stuck after {n} steps ({r2} R2 steps)" if n else f"not stuck in 10^5 steps ({r2} R2 steps)"))
        return
    T, H = int(argv[0]), int(argv[1])
    rng = random.Random(int(argv[2]) if len(argv) > 2 else 1)
    k = int(argv[3]) if len(argv) > 3 else 3
    trials = stuck = r2s = 0
    for t, s in snapshots(T):
        for _ in range(5):
            z, ch = perturb(s, k, rng)
            n, r2 = run(z, H)
            trials += 1
            r2s += r2
            if n:
                stuck += 1
                print(f"snapshot {t}, changes {ch}: stuck after {n} steps ({r2} R2 steps)", flush=True)
                if "-v" in os.environ.get("PERTURB_FLAGS", ""):
                    print("  ", z, flush=True)
    print(f"trials {trials}, stuck {stuck}, R2 steps {r2s}")


if __name__ == "__main__":
    main(sys.argv[1:])
