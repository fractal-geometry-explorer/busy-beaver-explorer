"""The carry of 1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC (and of 74982) after a conversion: a front in a
periodic background.

One sweep of the event system (`evstep`, lean/Ends.lean in the folder of 74982) sends a carry through the digits:

    state a: digit 0 -> 1, stop          digit 1 -> 0, go on in b
    state b: digit 0 -> 1, go on in a    digit 1 -> 0, go on in c
    state c: digit 0 -> 0, go on in c    digit 1 -> 1, go on in a

This script checks, by plain computation:

  tokens   the same sweep read as a rewriting of tokens:   0 -> 1 (stop),   10 -> 01,   1 1 0^j 1 -> 0^(j+2) 1
           (b is "flip the digit, then c"), on 20,000 random digit strings
  blocks   a block of three digits under carries in state a is a wheel of 8 positions that lets 3 carries of 8
           through (as a, b, c); the table of the wheel for carries a, b, c
  cycles   the cycles of the sweep on all strings of k digits, k <= 20 (a carry that leaves the string is dropped):
           the sweep is far from an odometer, the cycle of 1^k has 2^11 strings at k = 20
  through  the number of strings of k digits that a carry runs through: Fibonacci-like, ratio 1.618 per digit, so
           a fraction 0.809^k of all strings; a random string of k digits waits 1.236^k = 2^(0.306 k) sweeps
  front    the event system from the counter after the conversion of sweep 410,976 (410,922 ones, a 0, the 60
           marks, a 1) for S sweeps (default 2,000,000): the first sweep turns the ones into (001)^136,974; after
           that only a prefix is ever touched, and the digits behind the furthest carry are still 001001...
  period   the cycle of 1^k (2^e sweeps) and the number of carries that leave the k digits in one cycle, written
           out as a word, for k <= K (default 200): e is about 0.4 k and the word grows like 2^(0.1 k), so the
           exact carries of a prefix cannot be listed for 410,922 digits
  squares  the sweep to the power 2^j as an automaton on the first 60 digits (states = different sections):
           the number of states about triples with each squaring, so powers of the sweep cannot be tabulated

usage: python3 py/front.py [tokens|blocks|cycles|through|front [S]|period [K]|squares|all]
"""
import math
import random
import sys

ACT = {('a', 0): (1, None), ('a', 1): (0, 'b'), ('b', 0): (1, 'a'), ('b', 1): (0, 'c'),
       ('c', 0): (0, 'c'), ('c', 1): (1, 'a')}
YT = "101011011111011001101011001110000000011111111010101100011111"   # lean/Twin132695.lean (folder of 74982)
ONES = 410922


def carry(xs, q='a'):
    """The carry on a copy of xs: (digits after, state it leaves in or None if it stopped)."""
    xs = list(xs)
    for i, x in enumerate(xs):
        xs[i], q = ACT[(q, x)]
        if q is None:
            break
    return xs, q


def token_sweep(xs):
    """The same by tokens.  (digits after, True if the carry ran off the end)."""
    out, i, n = [], 0, len(xs)
    while i < n:
        if xs[i] == 0:
            return out + [1] + list(xs[i + 1:]), False
        if i + 1 == n:                       # 1 and the string ends: the carry leaves in b
            return out + [0], True
        if xs[i + 1] == 0:
            out += [0, 1]
            i += 2
            continue
        j = i + 2
        while j < n and xs[j] == 0:
            j += 1
        out += [0] * (j - i)
        if j == n:                           # 1 1 0^j and the string ends: the carry leaves in c
            return out, True
        out.append(1)
        i = j + 1
    return out, True                         # the carry leaves in a


def tokens(trials=20000, seed=1):
    rng = random.Random(seed)
    for _ in range(trials):
        xs = [rng.randint(0, 1) for _ in range(rng.randint(0, 40))]
        ys, q = carry(xs)
        assert token_sweep(xs) == (ys, q is not None), xs
    print(f"tokens: the sweep is 0 -> 1 (stop), 10 -> 01, 1 1 0^j 1 -> 0^(j+2) 1 on {trials} random strings")


def blocks():
    wheel = [(0, 0, 0)]
    while True:
        v = tuple(carry(wheel[-1])[0])
        if v == wheel[0]:
            break
        wheel.append(v)
    assert len(wheel) == 8
    pos = {v: i for i, v in enumerate(wheel)}
    print("blocks: three digits under carries in state a are a wheel of 8 positions;")
    print("        position, digits, then for a carry a, b, c: new position / state the carry leaves in (- = stops)")
    for i, v in enumerate(wheel):
        cells = []
        for q in 'abc':
            ys, g = carry(v, q)
            cells.append(f"{q}: {pos[tuple(ys)]}/{g or '-'}")
        print(f"        {i}  {''.join(map(str, v))}   " + "   ".join(cells))


def sweep_int(v, n):
    q, i = 0, 0
    while i < n:
        x = (v >> i) & 1
        if q == 0:
            if x == 0:
                return v | (1 << i)
            v ^= 1 << i
            q = 1
        elif q == 1:
            v ^= 1 << i
            q = 0 if x == 0 else 2
        elif x == 1:
            q = 0
        i += 1
    return v


def cycles(kmax=20):
    print("cycles: k, number of cycles of the sweep on k digits, longest cycle, cycle of 1^k")
    for k in range(1, kmax + 1):
        size = 1 << k
        seen, count, longest, ones = bytearray(size), 0, 0, 0
        for s in range(size):
            if seen[s]:
                continue
            length, v, has = 0, s, False
            while not seen[v]:
                seen[v] = 1
                length += 1
                has = has or v == size - 1
                v = sweep_int(v, k)
            count += 1
            longest = max(longest, length)
            if has:
                ones = length
        print(f"        {k:2d}  {count:6d}  {longest:6d}  {ones:6d}")


def through(kmax=40):
    cnt = {'a': 1, 'b': 0, 'c': 0}            # strings of k digits that leave the carry in each state
    print("through: k, strings of k digits the carry runs through (leaving in a, b, c), share of all strings")
    for k in range(1, kmax + 1):
        cnt = {'a': cnt['b'] + cnt['c'], 'b': cnt['a'], 'c': cnt['b'] + cnt['c']}
        if k % 5 == 0:
            tot = sum(cnt.values())
            print(f"        {k:2d}  {tot:12d}  ({cnt['a']}, {cnt['b']}, {cnt['c']})  {tot / 2 ** k:.3e}"
                  f"  = 0.809^{math.log(tot / 2 ** k) / math.log(0.809017):.1f}")


def cind(xs):
    q, out = 'a', []
    for x in xs:
        q = ACT[(q, x)][1]
        out.append(1 if q == 'c' else 0)
    return out


def front(sweeps=2000000):
    marks = cind([int(c) for c in YT])
    xs = [1] * ONES + [0] + marks + [1]
    assert len(xs) == 410984
    q, far, i = 'a', 0, 0
    for i, x in enumerate(xs):                # the first sweep
        xs[i], q = ACT[(q, x)]
        if q is None:
            break
    assert i == ONES and xs[:ONES] == [0, 0, 1] * (ONES // 3) and xs[ONES] == 1
    print(f"front: sweep 1 runs through the {ONES:,} ones (they become (001)^{ONES // 3:,}) and stops on the 0 "
          f"after them")
    print("        sweep, digits reached by the furthest carry so far")
    far, rec = 0, []
    for t in range(2, sweeps + 1):
        q, i = 'a', 0
        while q is not None:
            xs[i], q = ACT[(q, xs[i])]
            i += 1
        if i > far:
            far = i
            rec.append((t, i))
            if len(rec) % 3 == 0:
                print(f"        {t:10,d}  {i}")
    assert far < ONES and xs[far + (-far) % 3:ONES] == [0, 0, 1] * ((ONES - far - (-far) % 3) // 3)
    t, i = rec[-1]
    print(f"        after {sweeps:,} sweeps the furthest carry reached digit {far}; the digits after it are still "
          f"001 001 ...: {i / math.log2(t):.2f} digits per doubling of the sweeps so far")
    print(f"        at that rate the carry needs about 2^{ONES * math.log2(t) / i:,.0f} sweeps to cross the "
          f"{ONES:,} digits")


def period(kmax=200):
    def image(w, x):
        out = []
        for q in w:
            x, g = ACT[(q, x)]
            if g:
                out.append(g)
        return ''.join(out), x

    print("period: k, e (the cycle of 1^k has 2^e strings), carries leaving the k digits in one cycle")
    w, e = 'a', 0
    for k in range(1, kmax + 1):
        o, x = image(w, 1)
        if x != 1:                            # an odd number of carries a, b: the digit needs two rounds
            o2, x = image(w, x)
            o, e = o + o2, e + 1
        w = o
        if k <= 16:
            assert 2 ** e == cycle_of_ones(k)
        if k % 10 == 0:
            print(f"        {k:3d}  {e:3d}  {len(w):9,d}  = 2^{math.log2(len(w)):.1f}")


def cycle_of_ones(k):
    v, n = sweep_int((1 << k) - 1, k), 1
    while v != (1 << k) - 1:
        v, n = sweep_int(v, k), n + 1
    return n


def squares(depth=60, jmax=10):
    sys.setrecursionlimit(100000)
    tab, nodes, memo = {}, [], {}

    def mk(perm, c0, c1):
        k = (perm, c0, c1)
        r = tab.get(k)
        if r is None:
            r = tab[k] = len(nodes)
            nodes.append(k)
        return r

    z = mk(0, -1, -1)
    ident, a, b, c = [z], [z], [z], [z]
    for d in range(1, depth + 1):
        ident.append(mk(0, ident[-1], ident[-1]))
        a.append(mk(1, ident[d - 1], b[d - 1]))
        b.append(mk(1, a[d - 1], c[d - 1]))
        c.append(mk(0, c[d - 1], a[d - 1]))

    def mul(g, h):
        if g == z:
            return z
        r = memo.get((g, h))
        if r is None:
            pg, g0, g1 = nodes[g]
            ph, h0, h1 = nodes[h]
            r = mk(ph, mul(g0, h0), mul(g1, h1)) if pg == 0 else mk(1 ^ ph, mul(g0, h1), mul(g1, h0))
            memo[(g, h)] = r
        return r

    def size(g):
        seen, st = set(), [g]
        while st:
            x = st.pop()
            if x >= 0 and x not in seen:
                seen.add(x)
                st += nodes[x][1:]
        return len(seen)

    print(f"squares: j, states of the automaton of (sweep)^(2^j) on the first {depth} digits")
    g = a[depth]
    for j in range(jmax + 1):
        print(f"        {j:2d}  {size(g):8,d}")
        g = mul(g, g)


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "all"
    if cmd in ("tokens", "all"):
        tokens()
    if cmd in ("blocks", "all"):
        blocks()
    if cmd in ("cycles", "all"):
        cycles(20 if cmd == "cycles" else 16)
    if cmd in ("through", "all"):
        through()
    if cmd in ("front", "all"):
        front(int(sys.argv[2]) if len(sys.argv) > 2 else 2000000)
    if cmd in ("period", "all"):
        period(int(sys.argv[2]) if len(sys.argv) > 2 else 200)
    if cmd in ("squares", "all"):
        squares()
