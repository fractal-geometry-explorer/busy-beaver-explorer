"""The E-event map of 1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB, checked against direct simulation and iterated.

E(a, m) = `1 0 0 (10)^a 0^m E> 1` (blank elsewhere; E reads the last 1 of the tape).  For a >= 1 (and for a = 0
when m = 2 mod 3) the machine goes from E(a, m) to the next E-configuration E(a', m') in t steps:

    m = 3k     ->  E(a + 6, 4k + 4)    t = 4k^2 + 23k + 16a + 94
    m = 3k + 1 ->  E(a - 1, 4k + 7)    t = 4k^2 + 23k + 28
    m = 3k + 2 ->  E(a + 4, 4k + 4)    t = 4k^2 + 23k + 8a + 56

usage: python3 emap.py grid AMAX MMAX      direct simulation from every E(a, m), 1 <= a < AMAX, 2 <= m < MMAX
       python3 emap.py blank STEPS         the E-events of the run from blank tape, each checked against the map
       python3 emap.py far N               N more map steps after the last E-event below 1.1e10 steps
"""
import os, re, sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..",
                                "1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---", "py"))
import g01tools as g  # noqa: E402

M = "1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB"
PAT = re.compile(r"100((?:10)*)(0*)E1")
LAST = (10826674709, 58, 137643)   # the E-event of the blank run just below 1.1e10 steps (checked by `blank`)


def step(a, m):
    k, r = divmod(m, 3)
    if r == 0:
        return a + 6, 4 * k + 4, 4 * k * k + 23 * k + 16 * a + 94
    if r == 1:
        return a - 1, 4 * k + 7, 4 * k * k + 23 * k + 28
    return a + 4, 4 * k + 4, 4 * k * k + 23 * k + 8 * a + 56


def boundary(a, m):
    """where the map is not known to apply: the counter a is exhausted"""
    return a == 0 and m % 3 != 2


def direct(a, m, N=10**9):
    """the next E-event after E(a, m) by direct simulation: (a', m', t) or None"""
    for k, t in g.events(M, "1 00 (10)^%d 0^%d E> 1" % (a, m), N, "E", "R"):
        if isinstance(t, int):
            return None
        mm = PAT.fullmatch(t)
        if mm and k > 2:
            return len(mm.group(1)) // 2, len(mm.group(2)), k


def blank_events(N):
    for k, t in g.events(M, "A> 0", N, "E", "R"):
        if isinstance(t, int):
            return
        mm = PAT.fullmatch(t)
        if mm:
            yield k, len(mm.group(1)) // 2, len(mm.group(2))


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "grid":
        bad = n = 0
        for a in range(1, int(sys.argv[2])):
            for m in range(2, int(sys.argv[3])):
                n += 1
                if direct(a, m) != step(a, m):
                    bad += 1
                    print("MISMATCH", a, m, direct(a, m), step(a, m))
        print(f"grid: {n} starts, {bad} mismatches")
    elif cmd == "blank":
        prev, n = None, 0
        for k, a, m in blank_events(int(float(sys.argv[2]))):
            if prev and not boundary(prev[0], prev[1]):
                pa, pm, pk = prev
                assert step(pa, pm) == (a, m, k - pk), (prev, (a, m, k))
                n += 1
            prev = (a, m, k)
            print(k, a, m, "(boundary: the map does not apply)" if boundary(a, m) else "")
        print(f"blank: {n} E-events follow the map from the one before them, with exact step counts")
    elif cmd == "far":
        k, a, m = LAST
        mina = a
        for i in range(int(sys.argv[2])):
            if boundary(a, m):
                print("boundary reached after", i, "map steps")
                break
            k3, r = divmod(m, 3)              # the map without its step count (squaring m is the slow part)
            a, m = a + (6, -1, 4)[r], 4 * k3 + (4, 7, 4)[r]
            mina = min(mina, a)
        print(f"far: {i + 1} map steps after step {k}: a never below {mina}; now a = {a}, "
              f"m has {int(m.bit_length() * 0.30103) + 1} digits")
