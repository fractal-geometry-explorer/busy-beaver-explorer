"""The long-run dynamics of the return map G(a) = a + 12k(a) (py/returnmap.py): is it Collatz-like?

The return map takes [a, 2a+1] to [a+12k, 2(a+12k)+1] after 9k passes.  This file measures four things about it.

  orbit    G iterated from a = 5 (pass 3 of the blank orbit): k along the orbit, the values of a = 5 mod 12 that it
           skips, and v2(a-1).  G only ever adds 12k with k >= 1, so the orbit is a counter that steps through the
           values a = 5 mod 12 in order and skips the ones inside a jump (k >= 2).
  random   excursions from [a, 2a+1] for random a = 5 mod 12 of B bits: k, the number of low bits of a the route reads,
           and the margin x = log2(a / smallest stop block).  None of the three depends on B.
  tree     the class tree of returnmap.explore to depth D: the classes still open (their members read more than
           D+2 bits), how fast their number grows (the dimension of the set of 2-adic a whose route never ends),
           the worst margin, and the classes that halt or meet a stop block of 1 (none).
  mixing   at each open class, the block list as p + q*u where its parity became unknown: whether the u-coefficients
           repeat up to scale (a finite automaton would make them repeat), and which blocks have the odd coefficient.

usage:
  python3 py/dynamics.py orbit N          N returns of G from a = 5
  python3 py/dynamics.py random B N       N random a of B bits
  python3 py/dynamics.py tree D [D ...]   the class tree to depth D (D = 72: about 4 minutes)
  python3 py/dynamics.py mixing D         the open classes at depth D
"""
import collections
import math
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import passmap  # noqa: E402
import returnmap  # noqa: E402
from returnmap import Aff  # noqa: E402


def v2(x):
    return (x & -x).bit_length() - 1


def orbit(n, a=5):
    """The first n returns of G from a: list of (a, k)."""
    out = []
    for _ in range(n):
        g, passes, _ = returnmap.G(a)
        assert g is not None and (g - a) % 12 == 0 and passes == 9 * ((g - a) // 12)
        out.append((a, (g - a) // 12))
        a = g
    return out, a


def orbit_stats(seq, top):
    """k along the orbit; the values a = 5 mod 12 below top that the orbit skips, and whether they are exactly the
    values a + 12j, 0 < j < k(a), inside a jump."""
    visited = {a for a, _ in seq}
    skipped = [b for b in range(5, top, 12) if b not in visited]
    inside = {a + 12 * j for a, k in seq for j in range(1, k)}
    return {
        "k": sorted(collections.Counter(k for _, k in seq).items()),
        "values": len(range(5, top, 12)),
        "skipped": len(skipped),
        "skipped_are_jumps": set(skipped) == {b for b in inside if b < top},
        "v2_visited": sorted(collections.Counter(v2(a - 1) for a, _ in seq).items()),
        "v2_skipped": sorted(collections.Counter(v2(b - 1) for b in skipped).items()),
    }


def excursion(a, big=4096):
    """The excursion from [a, 2a+1] by the plain closed form, run beside a + 2^big (same route while the route reads
    fewer than `big` bits): (k, x, m) with x = log2(a / smallest stop block) and m the number of low bits of a the
    route depends on (the largest 2-adic denominator of a block's coefficient in a, plus the 2 bits of a = 1 mod 4)."""
    A = a + (1 << big)
    y, Y, small, m = [a, 2 * a + 1], [A, 2 * A + 1], None, 2
    while True:
        j = passmap.stop_index(y)
        assert j == passmap.stop_index(Y), "route reads more than `big` bits"
        if 1 <= j < len(y) and (small is None or y[j - 1] < small):
            small = y[j - 1]
        for u, w in zip(y, Y):
            m = max(m, big - v2(w - u) + 1)
        y, Y = passmap.passmap(y), passmap.passmap(Y)
        assert isinstance(y, list), (a, y)
        if len(y) == 2 and y[1] == 2 * y[0] + 1:
            return (y[0] - a) // 12, math.log2(a / small), m


def random_stats(bits, n, seed=1):
    rnd = random.Random(seed)
    ks, xs, ms = collections.Counter(), [], []
    for _ in range(n):
        a = 12 * rnd.getrandbits(bits - 4) + 5
        k, x, m = excursion(a)
        ks[k] += 1
        xs.append(x)
        ms.append(m)
    return {"k": sorted(ks.items()), "x_mean": sum(xs) / n, "x_max": max(xs),
            "m_mean": sum(ms) / n, "m_max": max(ms)}


def tree(depth):
    """returnmap.explore on a = 1 mod 4 down to mod 2^(depth+2)."""
    leaves, open_, points, bad = returnmap.explore(lambda a: [a, 2 * a + 1], [Aff(1, 4)], returnmap.two_block(1),
                                                   depth + 2)
    return {"routes": len(leaves), "open": len(open_), "bad": len(bad), "points": sorted(points),
            "dimension": math.log2(len(open_)) / depth if open_ else 0.0,
            "margin": returnmap.margins(leaves)[-1]}


def open_states(depth):
    """For each class open at depth `depth` (as in `tree`): the block list where its parity became unknown."""
    out, stack = [], [Aff(1, 4)]
    while stack:
        a = stack.pop()
        y = [a, 2 * a + 1]
        try:
            while True:
                z = returnmap.checked_pass(y)
                assert isinstance(z, list)
                if len(z) == 2 and z[1].q == 2 * z[0].q and z[1].p - 2 * z[0].p == 1:
                    break
                y = z
        except returnmap.Unknown:
            if a.q >= 2 ** (depth + 2):
                out.append((a, y))
            else:
                stack += [Aff(a.p, 2 * a.q), Aff(a.p + a.q, 2 * a.q)]
        except returnmap.Small:
            stack.append(Aff(a.p + a.q, a.q))
    return out


def mixing(depth):
    """The u-coefficients of the open states up to scale, and the blocks with an odd coefficient."""
    states = open_states(depth)
    shapes, odd, nums = set(), collections.Counter(), []
    for a, y in states:
        g = math.gcd(*[v.q for v in y])
        shapes.add(tuple(v.q // g for v in y))
        odd[(len(y), tuple(i for i, v in enumerate(y) if v.q % 2))] += 1
        nums.append(max(v.q // g for v in y))
    return {"open": len(states), "shapes": len(shapes), "odd_blocks": sorted(odd.items()),
            "largest_coefficient_bits": max(n.bit_length() for n in nums) if nums else 0}


def main(argv):
    if not argv:
        print(__doc__)
    elif argv[0] == "orbit":
        seq, top = orbit(int(argv[1]))
        s = orbit_stats(seq, top)
        print(f"{len(seq)} returns from a = 5 up to a = {top}")
        print("k along the orbit:", s["k"])
        print(f"values a = 5 mod 12 below it: {s['values']}, skipped {s['skipped']}"
              f" ({s['skipped'] / s['values']:.4f}); the skipped ones are exactly those inside a jump:"
              f" {s['skipped_are_jumps']}")
        print("v2(a-1) of the visited a:", s["v2_visited"])
        print("v2(a-1) of the skipped a:", s["v2_skipped"])
    elif argv[0] == "random":
        bits, n = int(argv[1]), int(argv[2])
        s = random_stats(bits, n)
        print(f"{n} random a = 5 mod 12 of {bits} bits: k {s['k']}; margin x mean {s['x_mean']:.2f} max"
              f" {s['x_max']:.2f}; bits read mean {s['m_mean']:.1f} max {s['m_max']}")
    elif argv[0] == "tree":
        for d in map(int, argv[1:]):
            s = tree(d)
            print(f"depth {d} (mod 2^{d + 2}): routes {s['routes']}, open {s['open']}"
                  f" (log2(open)/depth {s['dimension']:.3f}), bad {s['bad']}, set aside {s['points']},"
                  f" worst margin (m, x) {s['margin']}", flush=True)
    elif argv[0] == "mixing":
        s = mixing(int(argv[1]))
        print(f"open classes {s['open']}, distinct coefficient vectors up to scale {s['shapes']},"
              f" largest coefficient {s['largest_coefficient_bits']} bits")
        print("(blocks, blocks with odd coefficient):", s["odd_blocks"])
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
