"""The macro machine of 1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC.

X(n, m) = 0^inf C>0 0^n 1^m 0 1 0^inf  (C on the leftmost cell, n even).

    m >= 2:  n = 0 mod 4 -> X(3n/2 + 4, m - 1);   n = 2 mod 4 -> X((3n + 10)/2, m - 2)
    m = 1:   n = 0 mod 4 -> X(3n/2 + 4, 0);       n = 2 mod 4 -> X(4, 3n/2 + 6)   (a new epoch)
    m = 0:   n = 0 mod 4 -> X(4, 3n/2 + 5);       n = 2 mod 4 -> halt

With y = n/2 + 4 the first line is y -> ceil(3y/2), m -= 1 (y even) or 2 (y odd).  From blank tape the run reaches
X(4, 5) after 50 steps.

    python3 py/macro.py check     # the rules against direct simulation, n < 60 even, m < 12
    python3 py/macro.py epochs    # the first epochs exactly (plain big integers); py/epoch.py runs the third fast
"""
import re
import sys

sys.set_int_max_str_digits(0)
M = "1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC"


def mstep(n, m):
    if m >= 2:
        return ("x", 3 * n // 2 + 4, m - 1) if n % 4 == 0 else ("x", (3 * n + 10) // 2, m - 2)
    if m == 1:
        return ("x", 3 * n // 2 + 4, 0) if n % 4 == 0 else ("x", 4, 3 * n // 2 + 6)
    return ("x", 4, 3 * n // 2 + 5) if n % 4 == 0 else ("halt",)


def table():
    T = {}
    for i, g in enumerate(M.split("_")):
        for s in (0, 1):
            t = g[3 * s:3 * s + 3]
            T[(i, s)] = None if t[0] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
    return T


def simulate(n, m, limit=10 ** 7):
    T = table()
    tape = {}
    for i in range(m):
        tape[1 + n + i] = 1
    tape[1 + n + m + 1] = 1
    pos, st, lo, hi = 0, 2, 0, n + m + 2
    for _ in range(limit):
        t = T[(st, tape.get(pos, 0))]
        if t is None:
            return ("halt",)
        tape[pos] = t[0]; pos += t[1]; st = t[2]
        hi = max(hi, pos)
        if pos < lo:
            lo = pos
            if st == 2:
                s = "".join(str(tape.get(i, 0)) for i in range(pos, hi + 1)).rstrip("0")
                mm = re.fullmatch(r"0(0*)(1*)01", s)
                if mm:
                    return ("x", len(mm.group(1)), len(mm.group(2)))
    return ("?",)


def check():
    bad = 0
    for n in range(0, 60, 2):
        for m in range(0, 12):
            if n == 0:
                continue   # n >= 4 always
            a, b = mstep(n, m), simulate(n, m)
            if a != b:
                bad += 1
                if bad < 6: print("mismatch", n, m, a, b)
    print("checked", "ok" if not bad else f"{bad} mismatches")
    return bad


def epochs():
    n, m, it = 4, 5, 0
    while True:
        r = mstep(n, m); it += 1
        if r[0] == "halt":
            print("halt after", it); return
        if r[1] == 4:
            print(f"macro step {it}: new epoch X(4, {r[2]})")
            if r[2] > 10 ** 6:
                print("run the next epoch with: python3 py/epoch.py", r[2], 22); return
        n, m = r[1], r[2]


if __name__ == "__main__":
    {"check": check, "epochs": epochs}[sys.argv[1]]()
