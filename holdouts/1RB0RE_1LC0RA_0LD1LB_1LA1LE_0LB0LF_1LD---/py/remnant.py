"""The phase map with remnants of 1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD--- (proved in ../lean/Remnant.lean).

P(m, W) = 0^inf A> 1 1 1 0 10 1^m G(k1,c1) G(k2,c2) ... 0^inf with the remnant G(k, c) = 0 (10)^k 1^c.
`phase` is the same function as `phase` in Remnant.lean (next phase start and exact step count, None where not
covered).

usage: python3 remnant.py orbit      iterate from S(12) (step 75) until a case is not covered
       python3 remnant.py check N    compare N random cases with a direct simulation of the machine
"""
import random
import sys

sys.set_int_max_str_digits(0)
M = "1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---"


def rs(j, x):
    return j * (6 * x + 51) + 15 * j * (j - 1)


def phase(x, m, W):
    xp, R = x + 5 * (m // 3), rs(m // 3, x)
    if not W:
        if m % 3 == 0:
            return (2 * xp + 10, [], R + 4 * xp + 37 + 16)
        if m % 3 == 1:
            return (2 * xp + 12, [], R + 4 * xp + 41 + 16)
        return (2 * xp - 4, [(6, 4)], R + 4 * (xp - 8) + 115 + 16) if xp >= 8 else None
    (k, c), W2 = W[0], W[1:]
    if m % 3 == 0:
        if k == 0:
            return (2 * xp + 10 + c, W2, R + 4 * xp + 37 + 16)
        return (2 * xp + 11, [(k - 1, c)] + W2, R + 4 * xp + 37 + 16)
    if m % 3 == 1:
        r = phase(xp + k + 1, c, W2)
        return None if r is None else (r[0], r[1], R + r[2])
    if xp < 8:
        return None
    if c >= 3:
        return (2 * xp, [(k + 7, c - 3)] + W2, R + 6 * k + 4 * (xp - 8) + 109 + 16)
    if W2 or c == 2:
        return None
    return (2 * xp - 4, [(6, 2 * k + 4 + 2 * c)], R + 4 * k + 4 * (xp - 8) + 115 + 4 * c + 16)


def tape(m, W):
    s = "111010" + "1" * m
    for k, c in W:
        s += "0" + "10" * k + "1" * c
    return s


def run_to_restart(init, maxsteps):
    """Direct run from A> init (blank elsewhere) to the next phase start: (steps, tape) or None."""
    T = {}
    for i, g in enumerate(M.split("_")):
        for b in range(2):
            t = g[3 * b:3 * b + 3]
            T[(i, b)] = None if t[2] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
    pad = 1 << 16
    tp = bytearray(2 * pad)
    for i, ch in enumerate(init):
        tp[pad + i] = int(ch)
    p, s, n = pad, 0, 0
    while n < maxsteps:
        t = T[(s, tp[p])]
        if t is None:
            return None
        tp[p] = t[0]
        p += t[1]
        s = t[2]
        n += 1
        if s == 2 and tp[p] == 1 and not any(tp[p - 40:p]):  # C at the left end: restart follows (16 steps)
            hi = max(i for i in range(len(tp)) if tp[i])
            r = "".join(map(str, tp[p:hi + 1]))
            return n + 16, "111010" + r[2:]
    return None


def check(N):
    random.seed(1)
    ok = 0
    for _ in range(N):
        m = random.randint(0, 60)
        W = [(random.randint(0, 8), random.randint(0, 9)) for _ in range(random.choice([0, 0, 1, 1, 2]))]
        r = phase(1, m, W)
        if r is None:
            continue
        got = run_to_restart(tape(m, W), 10 ** 7)
        assert got is not None and got[1].rstrip("0") == tape(r[0], r[1]).rstrip("0") and got[0] == r[2], (m, W, r, got)
        ok += 1
    print(ok, "cases agree (phase start and step count)")


def orbit():
    m, W, t, n = 12, [], 75, 0
    while True:
        r = phase(1, m, W)
        if r is None:
            break
        m, W, t = r[0], r[1], t + r[2]
        n += 1
        if n <= 20 or n % 10000 == 0:
            print(n, "m:", m if n <= 20 else f"{m.bit_length()} bits", "W:", W, "step:", t if n <= 20 else f"{t.bit_length()} bits")
    print(f"{n} phases covered; then m = {m % 3} mod 3 before {W} (m of {m.bit_length()} bits, step of {t.bit_length()} bits)")


if __name__ == "__main__":
    if sys.argv[1] == "check":
        check(int(sys.argv[2]))
    else:
        orbit()
