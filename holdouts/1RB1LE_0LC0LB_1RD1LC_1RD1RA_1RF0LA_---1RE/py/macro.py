"""The macro machine of 1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE.

X(k, m) = 0^inf A>0 0 (10)^k 1^m 0 0^inf  (A on the cell left of the tape, blank to its left).

    m >= 4, or m = 3 and k even:  k = 2j -> X(3j + 3, m - 2);   k = 2j + 1 -> X(3j + 5, m - 3)
    m = 3, k = 2j + 1:  X(3j + 4, 1)
    m = 2:  k even -> X(2, 3k + 5);   k odd -> halt
    m = 1:  k odd  -> X(2, 3k + 3);   k even -> D runs right on blank tape forever ("drun")
    m = 0:  k even -> X(2, 3k);       k odd  -> drun

With y = k + 6 the first line is y -> ceil(3y/2), m -= 2 (y even) or 3 (y odd).  From blank tape the run reaches
X(1, 1) after 24 steps.

    python3 py/macro.py check      # every rule against direct simulation, k < 40, m < 14
    python3 py/macro.py epochs     # the run, epoch by epoch, exactly
    python3 py/macro.py odds       # the probability of each ending of an epoch with random parities
"""
import re
import sys
from fractions import Fraction

sys.set_int_max_str_digits(0)
M = "1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE"


def mstep(k, m):
    if m >= 4 or (m == 3 and k % 2 == 0):
        return ("x", 3 * (k // 2) + 3, m - 2) if k % 2 == 0 else ("x", 3 * (k // 2) + 5, m - 3)
    if m == 3:
        return ("x", 3 * (k // 2) + 4, 1)
    if m == 2:
        return ("x", 2, 3 * k + 5) if k % 2 == 0 else ("halt",)
    if m == 1:
        return ("x", 2, 3 * k + 3) if k % 2 == 1 else ("drun",)
    return ("x", 2, 3 * k) if k % 2 == 0 else ("drun",)


def simulate(k, m, limit=10 ** 7):
    """Direct simulation from X(k, m) to the next X, a halt, or D on blank tape to the right of everything."""
    tape = {}
    for i in range(k):
        tape[2 + 2 * i] = 1
    x = 2 + 2 * k
    for i in range(m):
        tape[x + i] = 1
    pos, st, lo, hi = 0, 0, 0, x + m
    T = {}
    for i, g in enumerate(M.split("_")):
        for s in (0, 1):
            t = g[3 * s:3 * s + 3]
            T[(i, s)] = None if t[0] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
    for n in range(limit):
        t = T[(st, tape.get(pos, 0))]
        if t is None:
            return ("halt",)
        tape[pos] = t[0]; pos += t[1]; st = t[2]
        if pos < lo:
            lo = pos
            if st == 0:
                s = "".join(str(tape.get(i, 0)) for i in range(pos, hi + 1)).rstrip("0")
                mm = re.fullmatch(r"00((?:10)*)(1*)", s)
                if mm:
                    return ("x", len(mm.group(1)) // 2, len(mm.group(2)))
        if pos > hi:
            hi = pos
            if st == 3 and all(v == 0 for i, v in tape.items() if i >= pos):
                return ("drun",)
    return ("?",)


def check():
    bad = 0
    for k in range(1, 40):
        for m in range(0, 14):
            if k == 0 and m >= 3:
                continue    # k = 0 never occurs (k >= 1 always); the rule is stated for k >= 1
            a, b = mstep(k, m), simulate(k, m)
            if a != b:
                bad += 1
                if bad < 6: print("mismatch", k, m, a, b)
    print("checked", "ok" if not bad else f"{bad} mismatches")
    return bad


def epochs(maxm=10 ** 6):
    k, m, it = 1, 1, 0
    while True:
        r = mstep(k, m); it += 1
        if r[0] != "x":
            print("ends:", r[0], "after", it, "macro steps"); return
        if r[1] == 2:
            mm = r[2]
            print(f"macro step {it}: epoch ends at m = {m} with k of {len(str(k))} digits; new epoch X(2, m) with m = "
                  + (str(mm) if mm < 10 ** 12 else f"a {len(str(mm))}-digit number"))
            if mm > maxm:
                print("the next epoch needs about", f"{len(str(mm))}-digit", "macro steps: out of reach"); return
        k, m = r[1], r[2]


def odds():
    """Probability of each ending of an epoch started at a large m, parities fair and independent."""
    # land in {1, 2, 3} from above with steps -2/-3: P(3) = 2/5, P(2) = 2/5, P(1) = 1/5 (renewal density 2/5)
    land = {3: Fraction(2, 5), 2: Fraction(2, 5), 1: Fraction(1, 5)}
    half = Fraction(1, 2)
    out = {"reset": 0, "halt": 0, "drun": 0}
    out["reset"] += land[3] * half; out["drun"] += land[3] * half      # m=3: even -> 1 then odd/even; odd -> (.,1)
    out["reset"] += land[2] * half; out["halt"] += land[2] * half
    out["reset"] += land[1] * half; out["drun"] += land[1] * half
    for k_, v in out.items():
        print(k_, v)
    print("halting eventually:", out["halt"] / (out["halt"] + out["drun"]))


if __name__ == "__main__":
    {"check": check, "epochs": epochs, "odds": odds}[sys.argv[1]]()
