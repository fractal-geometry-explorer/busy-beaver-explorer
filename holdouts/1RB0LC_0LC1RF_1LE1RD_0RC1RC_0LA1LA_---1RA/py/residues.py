"""Residue and near-miss statistics of the orbit of the U/V map from U(4, 3) (the even-a half of `step` in emap.py).

By `halts_iff_coincidence` (lean/Coincidence.lean) the machine halts exactly when the orbit meets an event with a
and b even and b - a in {4, -2}.  This script tests whether a congruence could exclude that.

  python3 residues.py hits PASSES MMAX   first pass at which, for each modulus M <= MMAX, an even/even event has
                                         b - a = 4 or -2 (mod M); a modulus never met is printed (the Lean check
                                         `sweep_100k` is `hits 100000 10000`; 300000 30000 leaves only M = 24463)
  python3 residues.py equi PASSES        events with b - a = 4 or -2 (mod M) against the count if b - a were
                                         uniform on even residues, for M = 2^j 3^i
  python3 residues.py near PASSES        record lows of |b - a| / a at even/even events, the sign of b - a, and
                                         a mod 3 by letter
"""
import sys
import collections
import math

sys.set_int_max_str_digits(0)


def step(t, a, b):
    """the next event from t(a, b) with a even (emap.step restricted to even a); 'HALT' at b = 1, a = 0 mod 4"""
    U = t == "U"
    s, o = t, ("V" if U else "U")
    if b % 2 == 1:
        if a % 4 == 2:
            return (o, (3 * a + 10) // 2, b)
        if b == 1:
            return "HALT"
        if b == 3:
            return ("V", 4, (3 * a + 16) // 2) if U else ("V", 2, (3 * a + 22) // 2)
        if b == 5:
            return ("V", 4, (3 * a + 14) // 2) if U else ("U", 4, (3 * a + 18) // 2)
        return (s, (3 * a + (16 if U else 20)) // 2, b - 5)
    if b >= a + 4:
        return (s, 3 * a + (6 if U else 8), b - a - 3)
    if b <= a - 2:
        return (o, 3 * b + 4, a - b - 1)
    if b == a:
        return ("V", 4, 3 * a + 6) if U else ("V", 2, 3 * a + 9)
    return ("V", 2, 3 * a + 11) if U else ("V", 4, 3 * a + 10)


def even_events(passes):
    """(pass, letter, a, b) for the events with b even among the first `passes` passes from U(4, 3)"""
    e = ("U", 4, 3)
    for k in range(passes + 1):
        t, a, b = e
        if b % 2 == 0:
            yield k, t, a, b
        e = step(t, a, b)
        if e == "HALT":
            print("HALT after", k, "passes")
            return


def hits(passes, mmax):
    rem = set(range(1, mmax + 1))
    first = {}
    for k, t, a, b in even_events(passes):
        d = b - a
        for M in list(rem):
            r = d % M
            if r == 4 % M or r == (-2) % M:
                first[M] = k
                rem.discard(M)
        if not rem:
            break
    print(f"moduli 1..{mmax}: {len(first)} met, never met: {sorted(rem)}")
    if first:
        w = max(first.values())
        print("latest first meeting: pass", w, "for M =", [M for M in first if first[M] == w])


def equi(passes):
    L = [(t, b - a) for k, t, a, b in even_events(passes)]
    print(len(L), "even/even events")
    for M in [8, 16, 64, 256, 1024, 4096, 9, 27, 81, 243, 729, 72, 216, 648, 1944, 5832]:
        n = sum(1 for t, d in L if d % M in (4 % M, (-2) % M))
        # d is even: for even M there are M/2 classes, two of them hits; for odd M, M classes, two hits
        exp = len(L) * 2 / (M // 2 if M % 2 == 0 else M)
        print(f"M = {M:5d}: {n:6d} events with b - a = 4 or -2 (mod M), {exp:8.1f} if uniform")


def near(passes):
    pos = n = 0
    best = None
    a3 = collections.Counter()
    for k, t, a, b in even_events(passes):
        n += 1
        d = b - a
        pos += d > 0
        a3[(t, a % 3)] += 1
        la = math.log10(a) if a.bit_length() < 1000 else a.bit_length() * math.log10(2)
        ld = (math.log10(abs(d)) if abs(d).bit_length() < 1000 else abs(d).bit_length() * math.log10(2)) if d else -9
        if best is None or ld - la < best:
            best = ld - la
            print(f"pass {k:7d}: log10 a = {la:8.1f}, log10 |b - a| = {ld:8.1f}, log10 |b - a|/a = {best:6.2f}")
    print(f"{n} even/even events, b > a at {pos}; (letter, a mod 3): {dict(a3)}")


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "hits":
        hits(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == "equi":
        equi(int(sys.argv[2]))
    elif cmd == "near":
        near(int(sys.argv[2]))
