"""The E-event map of 1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD.

An E-event is the head, in state E, at the left end of the tape, reading the first of six 0s:

    E> 0^6 (10)^n T          (blank beyond T; n maximal, so T never starts with 10)

From blank tape the first is (T, n) = (1, 0) at step 18.  The tail T is always one of

    1,   X_k = 000 (10)^k 1,   Y_k = 11 (01)^k,   Z_k = 000 (10)^k 0001

and the next E-event is (T', n') with n' = (3n + c)/2 for T = 1 or Z_k and n' = (9n + c)/8 for X_k and Y_k:

    1:    n even -> 1, (3n+6)/2;     n odd -> X_0, (3n+1)/2
    Z_k:  n even -> 1, (3n-d)/2;     n odd -> X_0, (3n-d-5)/2,     d = 6 floor((3k-2)/2)     (valid for n >= 12k+12)
    X_k, n mod 8 = 0..7:   Y_{k-1}  Y_k  X_{k+1}  X_k  X_{k+1}  Y_{k-2}  Y_{k-1}  M(k)      c = 24 15 -2 13 4 27 18 1
    Y_k, n mod 8 = 0..7:   Y_{k-2}  Y_{k-1}  M(k)  Y_{k-1}  Y_k  X_{k+1}  X_k  X_{k+1}      c = 24 15 -2 21 12 -5 10 1

with M(k) = X_{3k/2+3} for even k and Z_{(3k+1)/2} for odd k.  Going below index 0: X_0 and Y_0 with index -1 give
1; X_k at n = 5 (mod 8): k = 1 gives 1 and k = 0 gives X_0 with c = 19; Y_k at n = 0 (mod 8): k = 1 gives 1 and
k = 0 gives X_0 with c = 16.  So n grows by 3/2 (tail 1) or by 9/8 (tails X, Y) per pass, and the index k is a
second counter that moves by -2..+1, or is multiplied by 3/2 when n = 7 (mod 8) (X) or 2 (mod 8) (Y).  A phase of
X/Y tails ends when k runs out (back to tail 1) or at a Z_k, which subtracts about 4.5k from 1.5n.

The X and Y rules hold for every n >= 0 (checked); Z_k needs n >= 12k + 12, below that the tail becomes more
complicated and the machine can halt (e.g. Z_15 with n = 189).

usage: python3 emap.py rule TAIL               the eight rules of a tail, measured by direct simulation (rules.json)
       python3 emap.py grid KMAX NMAX          the map against direct simulation for k < KMAX and NMAX values of n
       python3 emap.py blank STEPS            the E-events of the blank run, each checked against the map
       python3 emap.py far N                  N map steps from (1, 0); smallest margin n/(12k+12) at the Z-events (as a power of 2)
"""
import json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---", "py"))
import g01tools as g  # noqa: E402

M = "1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD"
PAT = re.compile(r"E000000((?:10)*)(.*)")
RF = os.path.join(HERE, "rules.json")
FIRST = (18, "1", 0, 0)
CX = [24, 15, -2, 13, 4, 27, 18, 1]
CY = [24, 15, -2, 21, 12, -5, 10, 1]


def parse(T):
    if T == "1":
        return ("1", 0)
    for f, p in (("X", r"000((?:10)*)1"), ("Y", r"11((?:01)*)"), ("Z", r"000((?:10)*)0001")):
        m = re.fullmatch(p, T)
        if m:
            return (f, len(m.group(1)) // 2)
    return None


def word(f, k):
    return {"1": "1", "X": "000" + "10" * k + "1", "Y": "11" + "01" * k, "Z": "000" + "10" * k + "0001"}[f]


def mult(k):
    return ("X", 3 * k // 2 + 3) if k % 2 == 0 else ("Z", (3 * k + 1) // 2)


def down(k, j):
    """Y_{k-j}, or what replaces it below 0"""
    return ("Y", k - j) if k >= j else None


def step(f, k, n):
    """the next E-event (f', k', n'), or None where the map is not known to apply (Z_k with n < 12k + 12)"""
    r = n % 8
    if f == "1":
        return ("1", 0, (3 * n + 6) // 2) if n % 2 == 0 else ("X", 0, (3 * n + 1) // 2)
    if f == "Z":
        if n < 12 * k + 12:
            return None
        d = 6 * ((3 * k - 2) // 2)
        return ("1", 0, (3 * n - d) // 2) if n % 2 == 0 else ("X", 0, (3 * n - d - 5) // 2)
    c = (CX if f == "X" else CY)[r]
    if f == "X":
        g2 = [down(k, 1), ("Y", k), ("X", k + 1), ("X", k), ("X", k + 1), down(k, 2), down(k, 1), mult(k)][r]
        if g2 is None:
            g2 = ("1", 0) if r != 5 or k == 1 else ("X", 0)
            if r == 5 and k == 0:
                c = 19
    else:
        g2 = [down(k, 2), down(k, 1), mult(k), down(k, 1), ("Y", k), ("X", k + 1), ("X", k), ("X", k + 1)][r]
        if g2 is None:
            g2 = ("1", 0) if r != 0 or k == 1 else ("X", 0)
            if r == 0 and k == 0:
                c = 16
    return g2[0], g2[1], (9 * n + c) // 8


def nxt(T, n, N=2 * 10**9):
    """next E-event after (T, n) by direct simulation: (T', n', steps), ('HALT', steps) or None"""
    for k, t in g.events(M, "E> 0^6 (10)^%d %s" % (n, " ".join(T)), N, "E", "L"):
        if isinstance(t, int):
            return ("HALT", t) if k == "halted" else None
        mm = PAT.fullmatch(t)
        if mm and k > 1:
            return mm.group(2), len(mm.group(1)) // 2, k


def rule(T, r, rules):
    """[T', A, D, c] for tail T and n = r mod 8, measured at two values of n, or ['HALT']"""
    key = f"{T},{r}"
    if key not in rules:
        base = 8 * max(25, 5 * len(T))
        n1, n2 = base + r, 2 * base + r
        o1, o2 = nxt(T, n1), nxt(T, n2)
        if o1[0] == "HALT":
            rules[key] = ["HALT"]
        else:
            assert o1[0] == o2[0], (T, r, o1, o2)
            A, D = (3, 2) if (o2[1] - o1[1]) * 2 == 3 * base else (9, 8)
            assert (o2[1] - o1[1]) * D == A * base, (T, r, o1, o2)
            rules[key] = [o1[0], A, D, D * o1[1] - A * n1]
    return rules[key]


def blank_events(N):
    for k, t in g.events(M, "A> 0", N, "E", "L"):
        if isinstance(t, int):
            return
        mm = PAT.fullmatch(t)
        if mm and k >= FIRST[0]:
            yield k, mm.group(2), len(mm.group(1)) // 2


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "rule":
        rules = json.load(open(RF)) if os.path.exists(RF) else {}
        for r in range(8):
            R = rule(sys.argv[2], r, rules)
            f, k = parse(sys.argv[2])
            n = 800 + r
            p = step(f, k, n)
            agree = R[0] != "HALT" and p is not None and (word(p[0], p[1]), p[2]) == (R[0], (R[1] * n + R[3]) // R[2])
            print(sys.argv[2], "n = %d mod 8:" % r, R, "agrees with the map" if agree else "DISAGREES")
        json.dump(dict(sorted(rules.items())), open(RF, "w"), indent=0)
    elif cmd == "grid":
        K, NN = int(sys.argv[2]), int(sys.argv[3])
        bad = cnt = 0
        for f in "1XYZ":
            for k in (range(K) if f != "1" else [0]):
                lo = 12 * k + 12 if f == "Z" else 0
                for n in range(lo, lo + NN):
                    p = step(f, k, n)
                    d = nxt(word(f, k), n, 10**9)
                    cnt += 1
                    if d is None or d[0] == "HALT" or (word(p[0], p[1]), p[2]) != (d[0], d[1]):
                        bad += 1
                        print("MISMATCH", f, k, n, p, d, flush=True)
        print(f"grid: {cnt} starts, {bad} mismatches")
    elif cmd == "blank":
        prev, ok = None, 0
        for k, T, n in blank_events(int(float(sys.argv[2]))):
            p = parse(T)
            assert p is not None, T
            if prev:
                assert step(*prev) == (p[0], p[1], n), (prev, T, n, step(*prev))
                ok += 1
            prev = (p[0], p[1], n)
            print(k, T, n, flush=True)
        print(f"blank: {ok} consecutive E-events follow the map")
    elif cmd == "far":
        f, k, n = FIRST[1:]
        margin, kmax, zs, phases = None, 0, 0, 0
        for i in range(int(sys.argv[2])):
            if f == "Z":
                zs += 1
                m = n.bit_length() - (12 * k + 12).bit_length()
                margin = m if margin is None or m < margin else margin
            r = step(f, k, n)
            if r is None:
                print("not covered:", f, k, n)
                break
            if r[0] == "1" and f != "1":
                phases += 1
            f, k, n = r
            kmax = max(kmax, k)
        print(f"far: {i + 1} map steps from (1, 0): all covered; n has {int(n.bit_length() * 0.30103) + 1} digits; "
              f"largest index k = {kmax}; {zs} Z-events, {phases} returns to tail 1; "
              f"n/(12k+12) at a Z-event always at least 2^{margin - 1}")
