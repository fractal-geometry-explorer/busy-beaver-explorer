"""Searching for an inductive statement that bounds the first block: what is and is not inductive under the pass map.

Everything here runs on the closed form of the pass map (`py/passmap.py`, which `lean/Pass.lean` proves). A statement
P about block lists is *inductive* if every list with P (and the facts every orbit list has: `Good`, 4 | ones) that
neither halts nor meets a stop block of 1 goes to a list with P. The sections:

1. **Cases.** `case_image(y, j, half)` is the closed form for stop index j as an affine map with halves, `image` its
   integer version (tested against `passmap.passmap`), `linear_image` its linear part (constants dropped).
2. **Exact closure of linear statements.** `z3_closed` (z3 is optional: `pip install z3-solver`) asks for a list of
   k <= K blocks with P whose image fails P. Unsat for every k and j proves closure for those lengths (the solver is
   trusted; this is not Lean). `houdini` finds the strongest inductive conjunction of a pool of facts
   `a*f >= b*g + c` over the features y1, y2, y3, the last two blocks and the sum. `exhaustive_closed` is the
   brute-force version the tests use.
3. **The free-parity game** (`free_parity_game`): constants dropped, an adversary picks every parity. It drives the
   first block / ones to 0 within 16 passes. So no statement made only of inequalities can be inductive.
4. **psi**, an exact second invariant: psi(y) = sum (-2)^(k-i) y_i = y_k - 2 y_(k-1) + 4 y_(k-2) - ..., which in the
   nearest-first lists of `lean/Pass.lean` is the fold psi [] = 0, psi (y :: ys) = y - 2 psi ys. For every pass that
   neither halts nor meets a stop block of 1,

       2 psi(next y) = -psi(y) + 3 (-2)^n - 7,      n = k - j, the number of blocks the sweep crosses past the last

   (`psi_step`; checked symbolically for k <= 12 and by brute force in the tests). On a two-block state [a, 2a+d],
   psi = d. The last block's parity is psi mod 2. psi is what the free-parity game ignores.
5. **The (k, psi, j) automaton.** Along the blank orbit, and along every excursion class of `py/returnmap.py`,
   (block count, psi, stop index) takes few values (`orbit_triples`, `class_triples`). `run_bound` gives the longest run of
   front stops in that graph with no other change to the first block. `shape_game` plays the free-parity game
   restricted to the graph's edges and gives the least first block / ones it reaches.

usage:
  python3 py/invsearch.py linear K          linear candidates and the Houdini conjunction, by z3, for k <= K
  python3 py/invsearch.py game D            the free-parity game to depth D
  python3 py/invsearch.py psi               psi_step checked symbolically (needs sympy) for k <= 12
  python3 py/invsearch.py triples N D       (k, psi, j) on N orbit passes and on excursion classes mod 2^(D+2),
                                            with the front-stop run bound and the shape game on each set
  python3 py/invsearch.py reduce [R]        the parity graph (every stop psi allows) with a cap on the blocks: front-stop
                                            run bound and shape game (R rounds at most)
  python3 py/invsearch.py loop              the halving loop of [110, 63, 23] in psi
"""
import collections
import fractions
import itertools
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import passmap  # noqa: E402

F = fractions.Fraction


# ---------------------------------------------------------------------------------------------------------------
# 1. The pass map on k blocks, case by case
# ---------------------------------------------------------------------------------------------------------------

def case_parities(k, j):
    """The parities a pass with stop index j (1 <= j <= k) needs, as {block index (1-based): parity}."""
    if j == k:
        return {k: 0}
    par = {k: 1, j: 1}
    for i in range(j + 1, k):
        par[i] = 0
    return par


def case_image(y, j, half):
    """The closed form of `passmap.passmap` for stop index j, on a list y of any number type, with `half(x, c)` =
    (x + c)/2 (exact on the right parity). The result starts with the blank blocks y_(-1), y_0 where they are kept;
    `strip_zeros` says how many to drop."""
    k = len(y)
    g = [0, 0] + list(y)

    def Y(i):
        return g[i + 1]

    if j == k:
        add = half(y[-1], 4)
        return [Y(i) for i in range(-1, k - 2)] + [Y(k - 2) + add, Y(k - 1) + add]
    h = {i: half(Y(i), 0) for i in range(j + 1, k)}
    h[k] = half(y[-1], 5)
    out = [Y(i) for i in range(-1, j - 2)] + [Y(j - 2) + half(Y(j), -1), Y(j - 1) + half(Y(j), 1) + h[j + 1]]
    return out + [h[i] + h[i + 1] for i in range(j + 1, k)] + [h[k] - 1]


def strip_zeros(out, k, j):
    """How many leading entries of `case_image` are the blank y_(-1), y_0 (0 for this case)."""
    if j == k:
        return min(2, k - 1)               # k = 2: y_0 + m + 2 is the new first block
    if j >= 3:
        return 2
    return 1 if j == 2 else 0


def image(y, j):
    """The image list for stop index j (integers with the parities `case_parities` says)."""
    out = case_image(y, j, lambda x, c: (x + c) // 2)
    return out[strip_zeros(out, len(y), j):]


def linear_image(y, j):
    """The linear part of the pass of case j (every constant dropped): the image of y minus the image of 0."""
    half = lambda x, c: x / 2          # noqa: E731
    out = case_image(list(y), j, half)
    out0 = case_image([0 * v for v in y], j, half)
    z = [a - b for a, b in zip(out, out0)]
    return tuple(z[strip_zeros(z, len(y), j):])


def new_length(k, j):
    if j == k:
        return 2 if k <= 2 else k - 1
    return k + 1 if j == 1 else (k if j == 2 else k - 1)


def good(y):
    return bool(y) and y[0] >= 1 and all(b >= 2 for b in y[1:])


# ---------------------------------------------------------------------------------------------------------------
# 2. Exact closure of linear statements
# ---------------------------------------------------------------------------------------------------------------

def exhaustive_closed(P, K, B, mod4=True):
    """Every list of 2..K blocks of size 1..B with Good, 4 | ones (if mod4) and P: its image (when the pass neither
    halts nor meets a stop block of 1) has P. Returns None, a counterexample (y, image), or (y, None) for a list with
    P that meets the stop block of 1."""
    for k in range(2, K + 1):
        for y in itertools.product(range(1, B + 1), repeat=k):
            y = list(y)
            if not good(y) or (mod4 and sum(y) % 4) or not P(y):
                continue
            z = passmap.passmap(y)
            if z is None:
                return (y, None)
            if isinstance(z, list) and not P(z):
                return (y, z)
    return None


def _z3_case(k, j):
    """A z3 solver with the integer list of case (k, j): Good, 4 | ones, the parities, no stop block of 1.
    Returns (solver, blocks, image)."""
    import z3
    s = z3.Solver()
    ys = [z3.Int(f"y{i}") for i in range(1, k + 1)]
    qs = [z3.Int(f"q{i}") for i in range(1, k + 1)]
    par = case_parities(k, j)
    for i, (yv, qv) in enumerate(zip(ys, qs), start=1):
        s.add(yv >= (1 if i == 1 else 2))
        if i in par:
            s.add(yv == 2 * qv + par[i])
    s.add(sum(ys) % 4 == 0)
    if j < k:
        s.add(ys[j - 1] >= 3)

    def half(x, c):
        i = next(n for n, t in enumerate(ys) if t.eq(x))
        return qs[i] + (c + par[i + 1]) // 2

    out = case_image(ys, j, half)
    z = [t if not isinstance(t, int) else z3.IntVal(t) for t in out[strip_zeros(out, k, j):]]
    return s, ys, z


def z3_closed(P, K):
    """For k = 2..K and every stop index: a list with P whose image fails P? P(ys) takes z3 terms.
    Returns [(k, j, 'closed' | 'cex' | 'unknown', blocks of the counterexample or None)]."""
    import z3
    res = []
    for k in range(2, K + 1):
        for j in range(1, k + 1):
            s, ys, z = _z3_case(k, j)
            s.add(P(ys))
            s.add(z3.Not(P(z)))
            v = s.check()
            cex = [s.model().eval(t, model_completion=True).as_long() for t in ys] if v == z3.sat else None
            res.append((k, j, {z3.unsat: "closed", z3.sat: "cex"}.get(v, "unknown"), cex))
    return res


FEATURES = ("y1", "y2", "y3", "pen", "last", "S")


def feat(ys, name):
    """A feature of a list (ints or z3 terms); None where the list is too short (the fact is then vacuous). pen and
    last (the two last blocks) need 3 blocks, so as not to repeat y1, y2."""
    k = len(ys)
    return {"y1": ys[0], "y2": ys[1] if k >= 2 else None, "y3": ys[2] if k >= 3 else None,
            "pen": ys[-2] if k >= 3 else None, "last": ys[-1] if k >= 3 else None, "S": sum(ys)}[name]


def pair_pool(coef=(1, 2, 3, 4), consts=(-8, -4, -3, -2, -1, 0, 1, 2)):
    """Facts a*f >= b*g + c for two different features."""
    return [(a, f, b, g, c) for f, g in itertools.permutations(FEATURES, 2) for a in coef for b in coef
            if not (a % 2 == 0 and b % 2 == 0) for c in consts]


def fact_holds(fact, ys):
    a, f, b, g, c = fact
    x, y = feat(ys, f), feat(ys, g)
    return True if x is None or y is None else a * x >= b * y + c


def fact_z3(fact, ys):
    import z3
    a, f, b, g, c = fact
    x, y = feat(ys, f), feat(ys, g)
    return z3.BoolVal(True) if x is None or y is None else a * x >= b * y + c


def fact_str(fact):
    a, f, b, g, c = fact
    cs = f" + {c}" if c > 0 else (f" - {-c}" if c else "")
    return f"{a if a > 1 else ''}{f} >= {b if b > 1 else ''}{g}{cs}"


def orbit_sample(n=100000, extra_a=(2 ** 24 + 1, 17762561, 2 ** 40 + 1, 101, 17)):
    """Lists of the blank orbit (after pass 30) and of the excursions from [a, 2a+1] for a few a."""
    out = [y for i, y in enumerate(passmap.orbit(n)) if i > 30]
    for a in extra_a:
        y = [a, 2 * a + 1]
        for _ in range(400):
            out.append(y)
            y = passmap.passmap(y)
            if len(y) == 2 and y[1] == 2 * y[0] + 1:
                break
    return out


def houdini(pool, K, sample):
    """Drop the facts false on the sample, then repeatedly every fact that some pass breaks from a list with all the
    remaining facts (z3, lengths 2..K). Returns the strongest inductive conjunction of the pool (for those lengths)."""
    import z3
    facts = [f for f in pool if all(fact_holds(f, y) for y in sample)]
    while True:
        dropped = set()
        for k in range(2, K + 1):
            for j in range(1, k + 1):
                s, ys, z = _z3_case(k, j)
                for f in facts:
                    s.add(fact_z3(f, ys))
                if s.check() == z3.unsat:
                    continue
                for f in facts:
                    if f not in dropped:
                        s.push()
                        s.add(z3.Not(fact_z3(f, z)))
                        if s.check() != z3.unsat:
                            dropped.add(f)
                        s.pop()
        if not dropped:
            return facts
        facts = [f for f in facts if f not in dropped]


def tightest(facts):
    """For each (a, f, b, g) the largest c."""
    best = {}
    for a, f, b, g, c in facts:
        best[(a, f, b, g)] = max(best.get((a, f, b, g), c), c)
    return sorted((a, f, b, g, c) for (a, f, b, g), c in best.items())


# ---------------------------------------------------------------------------------------------------------------
# 3. The free-parity game
# ---------------------------------------------------------------------------------------------------------------

def free_parity_game(depth, start=(F(1, 3), F(2, 3)), forbid=None, kmax=8, keep=4000):
    """Constants dropped, every stop index allowed (an adversary picks the parities); `forbid(prev_j, k, j)` can rule
    a choice out. Returns, per depth, the least first block / ones (the `keep` lowest states are kept per depth)."""
    layer = [(start, None)]
    best = []
    for _ in range(depth):
        nxt = set()
        for y, pj in layer:
            for j in range(1, len(y) + 1):
                if forbid and forbid(pj, len(y), j):
                    continue
                z = linear_image(y, j)
                if len(z) <= kmax:
                    nxt.add((z, j))
        layer = sorted(nxt, key=lambda t: t[0][0])[:keep]
        best.append(float(layer[0][0][0]))
    return best


def two_front(pj, k, j):
    """`front_twice` (lean/Front.lean): no two front stops in a row."""
    return pj == 1 and j == 1


# ---------------------------------------------------------------------------------------------------------------
# 4. psi
# ---------------------------------------------------------------------------------------------------------------

def psi(y):
    """sum (-2)^(k-i) y_i: the fold psi [] = 0, psi (y :: ys) = y - 2 psi ys on the nearest-first list."""
    p = 0
    for v in y:
        p = v - 2 * p
    return p


def psi_const(n):
    """2 psi(next) + psi = 3 (-2)^n - 7 for a pass whose sweep crosses n blocks past the last (n = k - j)."""
    return 3 * (-2) ** n - 7


def psi_step(p, n):
    """psi after the pass, from psi before it and n = k - j. Needs p = n mod 2 (even last iff psi even)."""
    q = psi_const(n) - p
    assert q % 2 == 0, (p, n)
    return q // 2


def psi_symbolic(kmax=12):
    """Check 2 psi(image) + psi(y) = 3(-2)^(k-j) - 7 as a polynomial identity for every case with k <= kmax."""
    import sympy as sp
    for k in range(1, kmax + 1):
        for j in range(1, k + 1):
            par = case_parities(k, j)
            q = sp.symbols(f"q1:{k + 1}")
            ys = [2 * q[i] + par[i + 1] if i + 1 in par else sp.Symbol(f"y{i + 1}") for i in range(k)]
            z = case_image(ys, j, lambda x, c: (x + c) / sp.Integer(2))
            z = z[strip_zeros(z, k, j):]
            assert sp.expand(2 * psi(z) + psi(ys) - psi_const(k - j)) == 0, (k, j)
    return True


def loop_psi(y):
    """The orbit of y with psi and the stop index of each pass, until the event or a halt."""
    out = []
    while isinstance(y, list):
        out.append((y, psi(y), passmap.stop_index(y)))
        y = passmap.passmap(y)
    return out, y


# ---------------------------------------------------------------------------------------------------------------
# 5. The (k, psi, j) automaton
# ---------------------------------------------------------------------------------------------------------------

def step_state(k, p, j):
    """(k, psi) after a pass with stop index j."""
    return new_length(k, j), psi_step(p, k - j)


def orbit_triples(n):
    """(k, psi, j) along the first n passes from blank tape, after pass 30, with counts."""
    T = collections.Counter()
    for i, y in enumerate(passmap.orbit(n)):
        if i > 30:
            T[(len(y), psi(y), passmap.stop_index(y))] += 1
    return T


def class_triples(depth):
    """(k, psi, j) along every excursion class a = 1 mod 4 of `returnmap.explore`, split down to mod 2^(depth+2)
    (the pass whose stop is not yet known in an open class is left out). psi is the same on the whole class."""
    import returnmap as R
    Aff = R.Aff

    def psi_aff(y):
        p = Aff(0, 0)
        for v in y:
            p = v + (-2) * p
        return p

    T = collections.Counter()
    stack = [Aff(1, 4)]
    while stack:
        a = stack.pop()
        y, trip = [a, 2 * a + 1], []
        try:
            for _ in range(10 ** 4):
                p = psi_aff(y)
                assert p.q == 0, p
                trip.append((len(y), p.p, passmap.stop_index(y)))
                y = R.checked_pass(y)
                if len(y) == 2 and y[1].q == 2 * y[0].q and y[1].p - 2 * y[0].p == 1:
                    break
        except R.Unknown:
            trip.pop()
            if a.q < 2 ** (depth + 2):
                stack += [Aff(a.p, 2 * a.q), Aff(a.p + a.q, 2 * a.q)]
        except R.Small:
            stack.append(Aff(a.p + a.q, a.q))
            continue
        for t in trip:
            T[t] += 1
    return T


def changes_first(k, j):
    """Does a pass with stop index j on k blocks change the first block other than by halving it (a front stop)?
    j = 2 replaces it by (y2 - 1)/2, j = 3 adds (y3 - 1)/2, an even last block on 2 or 3 blocks adds to it or makes
    a new one; j >= 4 and an even last block on 4 or more blocks leave it alone."""
    return (j in (2, 3) and j < k) or (j == k and k <= 3)


def graph_of(T):
    """The graph {(k, psi): [(j, (k', psi'))]} of a set of triples."""
    G = collections.defaultdict(list)
    for (k, p, j) in T:
        G[(k, p)].append((j, step_state(k, p, j)))
    return G


def parity_graph(K, six=False, flag=True, start=(2, 1)):
    """The graph reachable from `start` when every stop index psi allows is taken (an even last block iff psi is
    even, any j < k otherwise), with at most K blocks. With `flag` a state also records whether the pass into it was a
    front stop, and a front stop does not follow one (`front_twice`). With `six`, a front stop on K blocks is allowed
    when it gives an even psi on K + 1 blocks (so an even last block, which the next pass removes).
    States are (k, psi) or (k, psi, after_front_stop)."""
    s0 = start + (False,) if flag else start
    G, stack = collections.defaultdict(list), [s0]
    seen = {s0}
    while stack:
        s = stack.pop()
        k, p = s[0], s[1]
        for j in ([k] if p % 2 == 0 else range(1, k)):
            if flag and s[2] and j == 1:
                continue
            k2, p2 = step_state(k, p, j)
            if k2 > K and not (six and k2 == K + 1 and p2 % 2 == 0):
                continue
            t = (k2, p2, j == 1) if flag else (k2, p2)
            G[s].append((j, t))
            if t not in seen:
                seen.add(t)
                stack.append(t)
    return G


def run_bound(G):
    """The most front stops on a path of G with no other change to the first block (inf if such a path cycles)."""
    memo = {}

    def best(s, on):
        if s in on:
            return math.inf
        if s not in memo:
            memo[s] = max([best(t, on | {s}) + (j == 1) for j, t in G.get(s, []) if not changes_first(s[0], j)],
                          default=0)
        return memo[s]

    return max(best(s, frozenset()) for s in list(G))


def shape_game(G, start, grid=1e-3, max_rounds=500):
    """The free-parity game on the edges of G only: shapes (blocks / ones, constants dropped) moved by the linear part
    of each allowed case, from (state, shape) `start`. States are merged on a grid (log scale for the first block).
    Returns (least first block / ones, cells, rounds, converged)."""
    def key(s, y):
        return s, (round(math.log2(y[0]) * 8) if y[0] > 0 else None), tuple(round(v / grid) for v in y[1:])

    seen, frontier, least, rounds = {key(*start)}, [start], start[1][0], 0
    while frontier and rounds < max_rounds:
        rounds += 1
        new = []
        for s, y in frontier:
            for j, t in G.get(s, []):
                z = linear_image(y, j)
                kz = key(t, z)
                if kz not in seen:
                    seen.add(kz)
                    new.append((t, z))
                    least = min(least, z[0])
        frontier = new
    return least, len(seen), rounds, not frontier


START_SHAPE = (1 / 3, 2 / 3)


def write_triples(T, path, title):
    with open(path, "w") as f:
        f.write(f"# {title}\n# k psi j count\n")
        for (k, p, j), c in sorted(T.items()):
            f.write(f"{k} {p} {j} {c}\n")


def read_triples(path):
    T = collections.Counter()
    with open(path) as f:
        for line in f:
            if line.strip() and not line.startswith("#"):
                k, p, j, c = map(int, line.split())
                T[(k, p, j)] = c
    return T


def main(argv):
    if not argv:
        print(__doc__)
    elif argv[0] == "linear":
        K = int(argv[1])
        facts = tightest(houdini(pair_pool(), K, orbit_sample()))
        print(f"strongest inductive conjunction of the pool, k <= {K} (z3):")
        for f in facts:
            print("  ", fact_str(f))
    elif argv[0] == "game":
        d = int(argv[1])
        print("free parities:      ", ["%.2g" % v for v in free_parity_game(d)])
        print("no two front stops: ", ["%.2g" % v for v in free_parity_game(d, forbid=two_front)])
    elif argv[0] == "psi":
        print("2 psi(next) + psi = 3(-2)^(k-j) - 7 for every case with k <= 12:", psi_symbolic(12))
    elif argv[0] == "triples":
        n, d = int(argv[1]), int(argv[2])
        for name, T in ((f"orbit, {n} passes", orbit_triples(n)), (f"classes mod 2^{d + 2}", class_triples(d))):
            by_k = collections.defaultdict(set)
            for k, p, _ in T:
                by_k[k].add(p)
            print(f"{name}: {len(T)} triples (k, psi, j);", "; ".join(
                f"k={k}: psi {min(v)}..{max(v)}" for k, v in sorted(by_k.items())))
            G = graph_of(T)
            least, cells, rounds, conv = shape_game(G, ((2, 1), START_SHAPE))
            print(f"   front-stop run bound {run_bound(G)}; shape game: least first block / ones {least:.2g}"
                  f" ({cells} cells, {rounds} rounds, {'converged' if conv else 'not converged'})")
    elif argv[0] == "reduce":
        for K, six in ((4, False), (5, False), (5, True), (6, False)):
            G = parity_graph(K, six)
            least, cells, rounds, conv = shape_game(G, ((2, 1, False), START_SHAPE), max_rounds=int(argv[1]) if len(argv) > 1 else 300)
            print(f"at most {K} blocks{' (and 6 with an even last block)' if six else ''}: {len(G)} states,"
                  f" front-stop run bound {run_bound(G)}, least first block / ones {least:.2g}"
                  f" ({'converged' if conv else 'not converged'} after {rounds} rounds)")
    elif argv[0] == "loop":
        for y in ([110, 63, 23], [31, 156, 13]):
            out, end = loop_psi(y)
            for z, p, j in out:
                print(f"  psi {p:5d}  j {j}  {z}")
            print("  ->", end, "\n")
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
