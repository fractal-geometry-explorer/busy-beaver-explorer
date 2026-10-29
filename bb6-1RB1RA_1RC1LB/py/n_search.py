"""A search for an invariant of the super step that keeps N = 10 + sum p_l 2^(m-l) off the powers of two.

usage:
  python3 n_search.py residues K      N mod q, alone and jointly with N's bit length, over the first K super steps
  python3 n_search.py digits K        N's popcount and leading bits, and the blocks near the right end
  python3 n_search.py starts L K      the super step from every two-block start [a, b], 1 <= a, b <= L, for K steps

The machine halts iff N is a power of two at some super step (`waves.py`; computed, not proved in Lean).  Each test
asks whether the orbit from blank tape keeps a property that powers of two lack.  None does; see the entry of
October 29, 2026 in ../notes/LAB_NOTES.md for the numbers this prints and what they mean.  Everything here rests on
`waves.superstep`, which is computed and tested but not proved.
"""
import math
import sys
from collections import Counter

from waves import big_n, superstep

ODD_Q = range(3, 128, 2)


def orbit(k):
    """(n, P, N) for the first k super steps from blank tape."""
    P = [1, 6]
    for n in range(k):
        yield n, P, big_n(P)
        P, _, _ = superstep(P)
        if P is None:
            raise RuntimeError(f"halt at super step {n}")


def order2(q):
    o = 1
    while pow(2, o, q) != 1:
        o += 1
    return o


def residues(k, skip=1000):
    """For each odd q: the power-of-two residues mod q that N never takes, and the classes c mod ord_q(2) for which
    N never takes the residue of 2^a (a = c mod ord) while N has a + 1 bits.  The second test is the stronger one:
    a power of two of a + 1 bits is 2^a, so an invariant could link N's size to its residue."""
    orders = {q: order2(q) for q in ODD_Q}
    alone = {q: set() for q in ODD_Q}
    joint = {q: set() for q in ODD_Q}
    sizes = Counter()
    for n, P, N in orbit(k):
        if n < skip:
            continue
        a = N.bit_length() - 1
        sizes[a] += 1
        for q in ODD_Q:
            r = N % q
            alone[q].add(r)
            joint[q].add((a % orders[q], r))
    for q in ODD_Q:
        o = orders[q]
        miss_alone = sorted({pow(2, a, q) for a in range(o)} - alone[q])
        seen_classes = Counter(a % o for a in sizes.elements())
        miss_joint = [c for c in range(o) if (c, pow(2, c, q)) not in joint[q]]
        # a class seen at fewer than 20 q super steps is too thin to call a miss
        thin = [c for c in miss_joint if seen_classes[c] < 20 * q]
        real = [c for c in miss_joint if c not in thin]
        print(f"q={q:3d} ord={o:3d}  missed residues: {miss_alone or '-'}  "
              f"missed (size, residue) pairs: {real or '-'}" + (f"  (thin classes: {len(thin)})" if thin else ""))
    print("bit lengths of N:", sorted((a + 1, c) for a, c in sizes.items()))


def digits(k, skip=1000):
    """Popcount of N against its bit length (a power of two has popcount 1), the closest N comes to a power of two
    from above in leading bits, and the blocks at the right end, which are a finite-state gadget."""
    low_pop = {}
    best_lead = (0, None)
    right = [set() for _ in range(6)]
    for n, P, N in orbit(k):
        if n < skip:
            continue
        b = N.bit_length()
        pc = bin(N).count("1")
        if b not in low_pop or pc < low_pop[b][0]:
            low_pop[b] = (pc, n)
        z = b - 1 - (N - (1 << (b - 1))).bit_length()     # zeros right after the leading 1
        if z > best_lead[0]:
            best_lead = (z, n, b)
        if n % 4 == 0 and len(P) >= 8:
            for j in range(6):
                right[j].add(P[-1 - j])
    print("bit length: lowest popcount seen (at super step)")
    for b, (pc, n) in sorted(low_pop.items()):
        print(f"  {b:3d}: {pc:3d}  ({n})")
    print("most zeros after the leading 1 (zeros, super step, bit length):", best_lead)
    for j in range(6):
        vals = sorted(right[j])
        print(f"block m-{j} at super steps 0 mod 4: {len(vals)} values, {vals[:10]}{' ...' if len(vals) > 10 else ''}")


def starts(L, k):
    """Run the super step from every [a, b], 1 <= a, b <= L.  At each arrival at the left end the decisive number is
    d_1 (halt iff it is a power of two); if d_1 were a random integer that would happen with chance about
    1/(d_1 ln 2).  Prints the number of halts against that expectation."""
    halts = arrivals = 0
    expected = 0.0
    for a in range(1, L + 1):
        for b in range(1, L + 1):
            P = [a, b]
            for n in range(k):
                P, kind, v = superstep(P)
                if kind != "turn":
                    arrivals += 1
                    expected += 1 / (v * math.log(2))
                if P is None:
                    halts += 1
                    break
    print(f"{L * L} starts, {arrivals} arrivals at the left end, {halts} halts; "
          f"a random d_1 would give about {expected:.0f}")


if __name__ == "__main__":
    a = sys.argv[1:]
    if len(a) >= 2 and a[0] == "residues":
        residues(int(a[1]))
    elif len(a) >= 2 and a[0] == "digits":
        digits(int(a[1]))
    elif len(a) >= 3 and a[0] == "starts":
        starts(int(a[1]), int(a[2]))
    else:
        print(__doc__)
