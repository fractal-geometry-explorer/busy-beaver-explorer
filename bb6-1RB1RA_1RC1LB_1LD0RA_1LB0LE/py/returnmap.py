"""The return map of the pass map (py/passmap.py) on two-block states [a, 2a+d].

After pass 30 the orbit from blank tape keeps coming back to two-block states [a, 2a+d] with |d| <= 3.  Six of the
seven values of d lead to the next two-block state in one to three passes by a fixed formula (`CHAINS`), and all of
them end at d = 1.  So the return map is the map G on the states [a, 2a+1], a = 1 mod 4, and what is left is the
excursion from [a, 2a+1] to the next state [a', 2a'+1].

`explore` runs the closed form on residue classes a = p + q*u (u >= 0 free): the very code of `passmap.passmap`, on
values `Aff(p, q)` that know their parity while q is even.  When a parity is not known the class splits in two
(q doubles); when a block could be 1 or less for some u >= 0 at a place where that matters, the one value u = 0 is set
aside to be run concretely and the class moves on to u >= 1.  So a class that reaches [a', 2a'+1] does so for every
member, along one route, without a stop block of 1; a class still running at the depth limit is left open.

usage:
  python3 py/returnmap.py chains            the six short chains, checked on residue classes mod 4
  python3 py/returnmap.py classes D         excursions from [a, 2a+1] on classes mod 2^(D+2): routes by k, open classes,
                                            then every member a < 2^(D+2) of an open class run concretely
  python3 py/returnmap.py concrete N        G(a) for a = 5, 9, ..., 4N+1 by the plain closed form
  python3 py/returnmap.py orbit N           the states [a, 2a+1] of the first N passes from blank tape: a = 5 mod 12
"""
import collections
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import passmap  # noqa: E402


class Unknown(Exception):
    """The parity of a value is not the same on the whole class: split it."""


class Small(Exception):
    """A value could equal the constant it is compared with (or be < 1) for some u >= 0: set u = 0 aside."""


class Aff:
    """p + q*u for an unknown u >= 0, with q >= 0."""
    __slots__ = ("p", "q")

    def __init__(self, p, q):
        self.p, self.q = p, q

    @staticmethod
    def of(x):
        return x if isinstance(x, Aff) else Aff(x, 0)

    def __add__(self, o):
        o = Aff.of(o)
        return Aff(self.p + o.p, self.q + o.q)

    __radd__ = __add__

    def __sub__(self, o):
        assert not isinstance(o, Aff)
        return Aff(self.p - o, self.q)

    def __rmul__(self, c):
        assert not isinstance(c, Aff)
        return Aff(c * self.p, c * self.q)

    def __mod__(self, m):
        assert m == 2
        if self.q % 2:
            raise Unknown
        return self.p % 2

    def __floordiv__(self, m):
        assert m == 2 and self.q % 2 == 0
        return Aff(self.p // 2, self.q // 2)

    def __eq__(self, c):
        """Equal on the whole class (q = 0 and p = c), unequal on the whole class, or Small."""
        assert not isinstance(c, Aff)
        if self.q == 0:
            return self.p == c
        if c >= self.p and (c - self.p) % self.q == 0:
            raise Small
        return False

    def __hash__(self):
        return hash((self.p, self.q))

    def at(self, u):
        return self.p + self.q * u

    def __repr__(self):
        return f"{self.p}+{self.q}u" if self.q else str(self.p)


def checked_pass(y):
    """One pass of the closed form on a list of Aff, with the blocks at the next pass start >= 1 on the class."""
    out = passmap.passmap(y)
    if isinstance(out, list):
        for v in out:
            if v.p < 1:
                raise Small
    return out


def run_class(start, stop, max_passes):
    """Run the closed form from `start` (list of Aff) until `stop(y)` is true.  Returns (end, route, small) with route
    the (blocks, stop index) of each pass, small the stop block (one inside the list) with the least u coefficient,
    and end the final list, HALT, None (stop block of 1), or "long"."""
    y, route, small = start, [], None
    while len(route) < max_passes:
        j = passmap.stop_index(y)
        route.append((len(y), j))
        if 1 <= j < len(y) and (small is None or y[j - 1].q < small.q):
            small = y[j - 1]
        y = checked_pass(y)
        if not isinstance(y, list) or stop(y):
            return y, tuple(route), small
    return "long", tuple(route), small


def two_block(d):
    """stop(y): y is a two-block state [a, 2a+d] on the whole class (d the same for every member)."""
    def stop(y):
        if len(y) != 2:
            return False
        e = y[1] + (-2) * y[0]
        assert e.q == 0, "two blocks with d varying over the class"
        return d is None or e.p == d
    return stop


def explore(make, cls, stop, max_depth, max_passes=10 ** 4):
    """Classes a = p + q*u from `cls`, the start list `make(a)`; split on unknown parities up to q = 2^max_depth.

    Returns (leaves, open, points, bad): leaves maps ((s, d), route) to the classes that reach the two-block state
    [a + s, 2(a + s) + d] along that route (each with its smallest stop block, see `run_class`),
    open is the classes at the depth limit, points the single values set aside, bad the classes that halt or meet a
    stop block of 1 on the whole class."""
    leaves, open_, points, bad = collections.defaultdict(list), [], [], []
    stack = list(cls)
    while stack:
        a = stack.pop()
        try:
            end, route, small = run_class(make(a), stop, max_passes)
        except Unknown:
            if a.q >= 2 ** max_depth:
                open_.append(a)
            else:
                stack += [Aff(a.p, 2 * a.q), Aff(a.p + a.q, 2 * a.q)]
            continue
        except Small:
            points.append(a.p)
            stack.append(Aff(a.p + a.q, a.q))
            continue
        if not isinstance(end, list):
            bad.append((a, end, route))
            continue
        assert len(end) == 2 and end[0].q == a.q and end[1].q == 2 * a.q, (a, end)
        leaves[((end[0].p - a.p, end[1].p - 2 * end[0].p), route)].append((a, small))
    return leaves, open_, points, bad


# The six short chains: from [a, 2a+d] with a = r mod 4, the next two-block state is [a + s, 2(a + s) + d'] after n
# passes.  (3a + d = 0 mod 4 at every reachable two-block state, since a pass start has 4(n+1) ones.)
CHAINS = {  # d: (r, s, d', n)
    0: (0, 2, -2, 1),
    -2: (2, 1, -1, 1),
    2: (2, 3, -3, 1),
    -1: (3, 2, 1, 2),
    3: (3, 3, 2, 2),
    -3: (1, 3, 0, 3),
}


def check_chains():
    """Each chain of CHAINS on the class a = r + 4u, a >= 5: one route, the end CHAINS says, no point set aside
    except below 5."""
    for d, (r, s, d2, n) in CHAINS.items():
        leaves, open_, points, bad = explore(lambda a: [a, 2 * a + d], [Aff(r if r else 4, 4)], two_block(None), 4)
        assert not open_ and not bad and all(p < 5 for p in points), (d, open_, bad, points)
        assert len(leaves) == 1, (d, leaves)
        ((ends, route),) = leaves
        assert ends == (s, d2) and len(route) == n, (d, ends, route)
    return True


def G(a, max_passes=10 ** 5):
    """The next state [a', 2a'+1] from [a, 2a+1] by the plain closed form: (a', passes, smallest stop block), or
    (None, passes, end) if the orbit halts or meets a stop block of 1 first."""
    y, n, small = [a, 2 * a + 1], 0, None
    while n < max_passes:
        j = passmap.stop_index(y)
        if 1 <= j < len(y) and (small is None or y[j - 1] < small):
            small = y[j - 1]
        y = passmap.passmap(y)
        n += 1
        if not isinstance(y, list):
            return None, n, y
        if len(y) == 2 and y[1] == 2 * y[0] + 1:
            return y[0], n, small
    return None, n, "long"


def classes(depth):
    """Excursions from [a, 2a+1] on all classes a = 1 mod 4, split down to a mod 2^(depth+2)."""
    leaves, open_, points, bad = explore(lambda a: [a, 2 * a + 1], [Aff(1, 4)], two_block(1), depth + 2)
    byk = collections.Counter()
    for (ends, route), cl in leaves.items():
        s = ends[0]
        assert s % 12 == 0 and ends[1] == 1 and len(route) == 9 * (s // 12), (ends, route)
        byk[s // 12] += 1
    bound = 2 ** (depth + 2)
    concrete = {}
    for a in points + [c.p + c.q * u for c in open_ for u in range(0, (bound - c.p) // c.q + 1) if c.p + c.q * u < bound]:
        concrete[a] = G(a)
    return byk, leaves, open_, points, bad, concrete


def margins(leaves):
    """For each modulus 2^m of a leaf class a = p + 2^m u: the least ratio (u coefficient of a stop block) / 2^m over
    the classes and their stop blocks, as a power of two.  The stop blocks of the members are about that fraction of
    a, or more."""
    worst = {}
    for cl in leaves.values():
        for a, small in cl:
            if small is None:
                continue
            m = a.q.bit_length() - 1
            x = m - (small.q.bit_length() - 1)
            worst[m] = max(worst.get(m, 0), x)
    return sorted(worst.items())


def orbit_returns(n):
    """The states [a, 2a+1] among the first n pass starts from blank tape: list of (pass, a)."""
    return [(i, y[0]) for i, y in enumerate(passmap.orbit(n))
            if isinstance(y, list) and len(y) == 2 and y[1] == 2 * y[0] + 1]


def main(argv):
    if not argv:
        print(__doc__)
    elif argv[0] == "chains":
        check_chains()
        for d, (r, s, d2, n) in CHAINS.items():
            print(f"[a, 2a{d:+d}], a = {r} mod 4  ->  [a+{s}, 2(a+{s}){d2:+d}]  in {n} pass{'es' if n > 1 else ''}")
        print("checked on every class (a >= 5)")
    elif argv[0] == "classes":
        depth = int(argv[1])
        byk, leaves, open_, points, bad, concrete = classes(depth)
        print(f"a = 1 mod 4 split down to mod 2^{depth + 2}: {len(leaves)} routes")
        print("routes by k (G(a) = a + 12k, 9k passes):", sorted(byk.items()))
        print("bad classes:", len(bad))
        print("worst stop block / a by class modulus, (m, x) for 2^m and 2^-x:", margins(leaves))
        print("values set aside:", sorted(points))
        print(f"open classes: {len(open_)}, measure {len(open_)}/2^{depth} of a = 1 mod 4")
        bound = 2 ** (depth + 2)
        nbad = [a for a, r in concrete.items() if r[0] is None]
        ks = collections.Counter((r[0] - a) // 12 for a, r in concrete.items() if r[0] is not None)
        print(f"members below 2^{depth + 2} of open classes and set-aside values, run concretely: {len(concrete)};"
              f" k {sorted(ks.items())}; halting or stop block 1 at a = {sorted(nbad)}")
    elif argv[0] == "concrete":
        ks, small = collections.Counter(), None
        for t in range(1, int(argv[1]) + 1):
            a = 4 * t + 1
            g, n, s = G(a)
            assert g is not None and (g - a) % 12 == 0 and n == 9 * ((g - a) // 12), (a, g, n, s)
            ks[(g - a) // 12] += 1
            if small is None or s / a < small[0]:
                small = (s / a, a, s)
        print("k:", sorted(ks.items()))
        print("smallest stop block / a: %.4f at a = %d (%d)" % small)
    elif argv[0] == "orbit":
        r = orbit_returns(int(argv[1]))
        print("states [a, 2a+1]:", len(r), "first", r[:5], "last", r[-1])
        print("a mod 12:", sorted(collections.Counter(a % 12 for _, a in r).items()))
        steps = collections.Counter((b - a) // 12 for (_, a), (_, b) in zip(r, r[1:]))
        print("k = (a' - a)/12:", sorted(steps.items()))
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
