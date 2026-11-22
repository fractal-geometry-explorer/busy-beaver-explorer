"""What happens after a lost race (lean/Race.lean), by simulation.

A race is lost at a Q configuration (W, a, G) whose word has run out (W = [x] or [1, x], last block first) while a
misaligned gap (length not 3p + 2) is pending.  Lean proves that the macro map `astep` can fail only after one
(`inv_step`).  This script starts from random configurations right before an anomaly (one block x, low part a,
aligned gaps G; small a and x, so that races are often lost), iterates the macro map (`astep` of lean/Full.lean,
transcribed below with the word last block first) and, where it fails, runs the machine itself to see whether it
halts.  It prints how many orbits lost a race, how many of those reached a failure of the map, and how many of the
failures halt within the step limit.

usage: python3 lostrace.py [TRIALS] [MACRO_STEPS] [MACHINE_STEPS]     (defaults 400 2000 1000000)
"""
import random
import sys

M = "1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---"
TAB = {}
for i, s in enumerate(M.split("_")):
    for r in (0, 1):
        t = s[3 * r:3 * r + 3]
        TAB[("ABCDEF"[i], r)] = None if t[2] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, t[2])


def phi(W):
    return [1] * ((W[0] - 1) // 2) + [W[1] + 2] + W[2:] if len(W) >= 2 else list(W)


def lead2(G):
    t = 0
    while t < len(G) and G[t] == 2:
        t += 1
    return t, G[t:]


def coll(s, p, g, U):
    o = [1] * (3 * s)
    tab = {(0, 0, 0): ([3], 1, 0), (0, 0, 1): ([5], 1, 1), (0, 0, 2): ([7], 1, 2), (0, 1, 0): ([3], 1, 1),
           (0, 1, 1): ([5], 1, 2), (1, 0, 0): ([1, 1, 1], 1, 1), (1, 0, 1): ([3, 1, 1], 1, 2),
           (1, 1, 0): ([1, 1, 1], 1, 2), (1, 1, 1): ([1, 1, 1], 2, 2)}
    if (p, g, U) in tab:
        C, a, d = tab[(p, g, U)]
        return C + o, a, d
    if (p, g) == (0, 0) and U >= 3:
        return [7] + o, U - 1, 2
    if (p, g) == (0, 1) and U >= 2:
        return [5] + o, U, 2
    if (p, g) == (1, 0) and U >= 2:
        return [3, 1, 1] + o, U, 2
    if (p, g) == (1, 1) and U >= 2:
        return [1, 1, 1] + o, U + 1, 2
    return None


def fresh(x):
    return [1] * ((x - 2) // 2) + [2]


def astep(c):
    W, a, G = c
    if len(W) == 1:
        x = W[0]
        return (fresh(x), 1, [3 * (a - 1)] + G) if x % 2 == 0 and x >= 2 and a >= 1 else None
    if len(W) == 2 and W[0] == 1:
        x = W[1]
        if not (x % 2 == 0 and x >= 2):
            return None
        if a >= 2:
            return [3] + fresh(x), 1, [3 * (a - 2) + 1] + G
        t, R = lead2(G)
        if not R:
            return [5] + fresh(x), 1 if t == 0 else t + 1, []
        return ([5] + fresh(x), 1 if t == 0 else t + 1, [R[0] - 3] + R[1:]) if R[0] >= 3 else None
    b, x = W[0], W[1]
    if not ((b % 2 == 1 and b >= 3) or (b == 1 and x % 2 == 1 and len(W) > 2)):
        return None
    W2 = phi(phi(W))
    if a >= 2:
        return W2, 1, [3 * (a - 2) + 2] + G
    t, R = lead2(G)
    if not R:
        return W2, t + 2, []
    h, G0 = R[0], R[1:]
    if h >= 3:
        return W2, t + 2, [h - 3] + G0
    U, R2 = lead2(G0)
    C, a2, d = coll(t // 2, t % 2, h, U)
    W3 = C + [W2[0] + 2] + W2[1:]
    if not R2:
        return W3, a2, []
    return (W3, a2, [R2[0] - 5 + d] + R2[1:]) if R2[0] >= 5 else None


def lost(c):
    W, a, G = c
    return (len(W) == 1 or (len(W) == 2 and W[0] == 1)) and any(g % 3 != 2 for g in G)


def halts(c, limit):
    W, a, G = c
    tape = {}
    left = [1] * (3 * a) + [0]
    for b in W:
        left += [1] * b + [0]
    for i, v in enumerate(left):
        tape[-1 - i] = v
    p = 1
    for g in G:
        p += g
        tape[p] = 1
        p += 1
    pos, st = 0, "B"
    for n in range(limit):
        tr = TAB[(st, tape.get(pos, 0))]
        if tr is None:
            return n
        tape[pos] = tr[0]
        pos += tr[1]
        st = tr[2]
    return None


def main(trials, macro, limit):
    rnd = random.Random(3)
    nlost = nfail = nhalt = 0
    for _ in range(trials):
        c = ([rnd.choice(range(2, 16, 2))], rnd.randint(1, 12),
             [3 * rnd.choice([0, 0, 0, 1, 1, 2, 3, 5]) + 2 for _ in range(rnd.randint(0, 6))])
        was_lost = False
        for i in range(macro):
            if i and lost(c):
                was_lost = True
            c2 = astep(c)
            if c2 is None:
                assert was_lost or lost(c), c   # inv_step: a failure needs a lost race
                nfail += 1
                nhalt += halts(c, limit) is not None
                break
            c = c2
        nlost += was_lost
    print(f"{trials} orbits: {nlost} lost a race; the map failed on {nfail}; "
          f"the machine halts (within {limit} steps) from {nhalt} of these failures and not from {nfail - nhalt}")


if __name__ == "__main__":
    a = sys.argv[1:]
    main(int(a[0]) if a else 400, int(a[1]) if len(a) > 1 else 2000, int(a[2]) if len(a) > 2 else 10 ** 6)
