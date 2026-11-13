"""Check the phase map of 1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA against the machine, and estimate the halting
chance per cycle.

usage: python3 holdouts/1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA/py/m6check.py      (compiles ../c/m6c.c with gcc)

The phase start P m n is 0^inf (1011)^m 1^n (10)^3 A> 1 0^inf; c/m6c.c starts the machine there (its argument J is
n + 1) and reports the next phase start.  `nxt` is the map proved in lean/Map.lean (`next`).
"""
import os
import random
import subprocess
import sys
import tempfile

M = "1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA"
HERE = os.path.dirname(os.path.abspath(__file__))


def nxt(m, n):
    if n < 3:
        return None
    k, r = (n - 3) // 3, (n - 3) % 3
    if r == 0:
        return (m - 1, 8 * k + 19) if m >= 1 else (2 * k + 4, 5)
    if r == 1:
        if m >= 2:
            return (m - 2, 8 * k + 29)
        return None if m == 1 else (0, 8 * k + 18)
    if m >= 2:
        return (m - 2, 8 * k + 35)
    return (2 * k + 8, 5) if m == 1 else (0, 8 * k + 18)


def main():
    exe = os.path.join(tempfile.mkdtemp(), "m6c")
    subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(HERE, "..", "c", "m6c.c")], check=True)
    random.seed(0)
    cases = [(m, j) for m in range(8) for j in range(4, 60)]
    cases += [(random.randint(0, 60), random.randint(4, 400)) for _ in range(150)]
    bad = 0
    for m, j in cases:
        out = subprocess.run([exe, M, str(m), str(j), "2000000000", "1"], capture_output=True, text=True).stdout
        if out.startswith("HALT"):
            got = None
        else:
            f = dict(x.split("=") for x in out.split()[1:])
            mm, jj = int(f["m"]), int(f["j"])
            got = (mm, jj + 2 - 1 if mm == 0 else jj - 1)
        exp = nxt(m, j - 1)
        if got != exp:
            bad += 1
            print("MISMATCH", m, j - 1, exp, got)
    print(f"map vs machine: {len(cases)} phase starts, {bad} mismatches")
    sys.set_int_max_str_digits(0)
    o, resets = (14, 5), []
    for i in range(1, 6820):
        o = nxt(*o)
        if o[1] == 5:
            resets.append((i, len(str(o[0]))))
    print("resets of the orbit from (14, 5) (phase, digits of the new stack):", resets)
    h = c = 0
    for _ in range(4000):
        m, n = random.randint(200, 400), random.randint(10 ** 30, 10 ** 31)
        while True:
            s = nxt(m, n)
            if s is None:
                h += 1
                break
            if s[1] == 5 and m <= 1:
                c += 1
                break
            m, n = s
    print(f"random cycles: {h} halts, {c} resets, halting fraction {h / (h + c):.3f}")


if __name__ == "__main__":
    main()
