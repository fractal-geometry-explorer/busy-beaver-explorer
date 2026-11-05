"""The sentinel block of 3 and what it says about the excursions of the return map (notes/LAB_NOTES.md, 4 November).

phi(y) = y_1 ... y_(k-1) (y_k + 5) 3.  A pass commutes with phi exactly (`lean/Sentinel.lean`, `next_phi`, kernel):
passmap(phi(y)) = phi(passmap(y)), and so the orbit of phi(y) is phi of the orbit of y.

A last block that is 3 only modulo 2^r acts as a sentinel for about r passes (it goes 3 + 2^r w -> 3 + 2^(r-1) w).
So while a state's last block is 3 mod 2^r, the route of the pass map is the route of the list with that block
removed (phi^-1).  For a = 1 + 2^m u the first pass from [a, 2a+1] gives [2^(m-1) u, 5 + 3 2^(m-1) u, 3 + 2^m u],
which is phi([0]) modulo 2^(m-1): phi of blank tape.  So the excursion runs the blank-tape orbit:

    pass t+1 of the excursion  =  phi(orbit t)  modulo 2^(m-t-1), blockwise from the right (extra blocks on the
    left = 0), with the same sweep, for t = 0 .. m-2                                                    (`deep`)

The sizes are set by the high parts, a linear map along the blank orbit's route, and keep the first block about a/4
or more.  When the sentinel runs out, a new one usually forms with fresh bits and the inner counter goes on
(`phases`): the excursions that read many bits are the blank orbit run again inside, at the scale log a.

usage:
  python3 py/sentinel.py conj N             N random lists: passmap(phi(y)) = phi(passmap(y)), events included
  python3 py/sentinel.py deep M T           a = 1 + 2^M u, u = 1 and T - 1 random odd u: the congruence above for
                                            t = 0 .. M-2, the route, and the least first block / a after pass 5
  python3 py/sentinel.py phases D N         N members of the open classes mod 2^(D+2) (high bits random): the
                                            inner counter values x at each phase (the state, sentinel removed,
                                            brought to [x, 2x+1] by the short chains)
"""
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import passmap  # noqa: E402
import returnmap  # noqa: E402


def phi(y):
    """The sentinel map, first block first; blank tape is read as [0]."""
    y = list(y) or [0]
    return y[:-1] + [y[-1] + 5, 3]


def phiN(out):
    return phi(out) if isinstance(out, list) else out


def v2(x):
    return 10 ** 9 if x == 0 else (x & -x).bit_length() - 1


def conj(n, seed=1):
    """passmap(phi(y)) == phiN(passmap(y)) on n random lists (blocks 1..40, 1..8 blocks), counting the events."""
    rnd = random.Random(seed)
    events = {}
    for _ in range(n):
        y = [rnd.randint(1, 40) for _ in range(rnd.randint(1, 8))]
        out = passmap.passmap(y)
        assert passmap.passmap(phi(y)) == phiN(out), y
        if not isinstance(out, list):
            events[str(out)] = events.get(str(out), 0) + 1
    return events


def blank_orbit(n):
    """orbit[t] = the blank orbit at pass t, orbit[0] = [0] (blank tape as one empty block)."""
    return [[0]] + [y for _, y in zip(range(n - 1), passmap.orbit(n))]


def deep(m, u, orb=None):
    """Run [a, 2a+1], a = 1 + 2^m u, for m - 1 passes beside phi of the blank orbit.  Checks, for t = 0 .. m-2, that
    pass t+1 is phi(orbit t) modulo 2^(m-t-1) (aligned at the right, extra blocks on the left = 0 mod that) and that
    the sweep stops at the matching block, and that every block is at least its block of phi(orbit t) (the high
    part is never negative, so the stop block is at least the blank orbit's).  Returns the least first block / a over passes 6 .. m-1 and the least
    stop block / a."""
    orb = orb or blank_orbit(m)
    a = 1 + 2 ** m * u
    y, low, low_stop = [a, 2 * a + 1], None, None
    for t in range(m - 1):
        y = passmap.passmap(y)
        assert isinstance(y, list), (m, u, t, y)
        p = phi(orb[t])
        e = len(y) - len(p)
        assert e >= 0, (m, u, t)
        mod = 2 ** (m - t - 1)
        assert all(b % mod == 0 for b in y[:e]), (m, u, t)
        assert all((b - c) % mod == 0 for b, c in zip(y[e:], p)), (m, u, t)
        assert all(b >= c for b, c in zip(y[e:], p)), (m, u, t)        # the high part is >= 0 in every block
        j = passmap.stop_index(y)
        assert j == e + passmap.stop_index(p), (m, u, t)
        if t >= 5:
            f = y[0] / a
            low = f if low is None or f < low else low
            if j < len(y):
                s = y[j - 1] / a
                low_stop = s if low_stop is None or s < low_stop else low_stop
    return low, low_stop


def smallest(x, r):
    """x mod 2^r as the residue of least absolute value."""
    x %= 2 ** r
    return x if x < 2 ** (r - 1) else x - 2 ** r


def to_return_state(x, d):
    """Bring [x, 2x+d] to [x', 2x'+1] by the short chains (returnmap.CHAINS, which ignore the residue of x here)."""
    while d != 1:
        if d not in returnmap.CHAINS:
            return None
        _, s, d, _ = returnmap.CHAINS[d]
        x += s
    return x


def inner_values(a, min_r=6, max_passes=5000):
    """The excursion from [a, 2a+1]: at each three-block state whose last block is 3 mod 2^r, r >= min_r, the value
    x of the two-block list under the sentinel, read modulo 2^(r-2) and brought to [x, 2x+1]; consecutive repeats
    dropped.  Returns (list of (pass, x), passes to the return or None)."""
    y, xs = [a, 2 * a + 1], []
    for t in range(max_passes):
        r = v2(y[-1] - 3)
        if t > 0 and len(y) == 3 and r >= min_r:
            x0 = smallest(y[0], r - 2)
            x = to_return_state(x0, smallest(y[1] - 5 - 2 * y[0], r - 2))
            if x is not None and (not xs or xs[-1][1] != x):
                xs.append((t, x))
        y = passmap.passmap(y)
        if not isinstance(y, list):
            return xs, y
        if len(y) == 2 and y[1] == 2 * y[0] + 1:
            return xs, t + 1
    return xs, None


def open_members(depth, n, seed=1, high_bits=200):
    leaves, open_, points, bad = returnmap.explore(lambda a: [a, 2 * a + 1], [returnmap.Aff(1, 4)],
                                                   returnmap.two_block(1), depth + 2)
    rnd = random.Random(seed)
    return [c.p + c.q * rnd.getrandbits(high_bits) for c in sorted(open_, key=lambda c: c.p)[:n]]


def main(argv):
    if not argv:
        print(__doc__)
    elif argv[0] == "conj":
        ev = conj(int(argv[1]))
        print(f"{argv[1]} random lists: passmap(phi(y)) = phi(passmap(y)); events among them: {ev}")
    elif argv[0] == "deep":
        m, n = int(argv[1]), int(argv[2])
        rnd = random.Random(m)
        orb = blank_orbit(m)
        lows = []
        for i in range(n):
            u = 1 if i == 0 else 2 * rnd.getrandbits(64) + 1
            lows.append(deep(m, u, orb))
        print(f"a = 1 + 2^{m} u, {n} values of u: passes 1..{m - 1} are phi(blank orbit) mod 2^(m-t-1), same route,"
              " every block at least the blank orbit's")
        print("least first block / a after pass 5: %.5f; least stop block / a: %.5f"
              % (min(f for f, _ in lows), min(s for _, s in lows)))
    elif argv[0] == "phases":
        depth, n = int(argv[1]), int(argv[2])
        for a in open_members(depth, n):
            xs, end = inner_values(a)
            print(f"a mod 2^{depth + 2} = {a % 2 ** (depth + 2)}, v2(a-1) = {v2(a - 1)}: returns after {end};"
                  f" inner x by pass: {xs}")
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
