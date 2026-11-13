"""The level-1 rule of 1RB1LA_1RC0LD_1LB0RE_0LA0LC_0RD1RF_0RB---, checked by direct simulation.

With t = 110, the unit U = t^13 0 t^2 1 0 1 0 (50 cells) and the left end P = 1 0 t 1 0 1 0:

    0^inf P U^n t^(r+6) E> 0^inf   ->   0^inf P U^(n+1) t^r E> 0^inf     in 972 n + 48 r + 1014 steps

(the head in E on the first blank cell right of the tape).  Four sweeps add one unit and use six t of the
reservoir; the tape grows by 14 cells on the left and 18 on the right.  The script runs the machine from the left
configuration and checks that it reaches the right one after exactly that many steps, for n <= NMAX, r <= RMAX.
From blank tape the rule is first met at step 6,335 (n = 2, r = 5).  Not proved: tools/py/bbtools/symtm.py does
not find the rule (the sweeps do not cross a unit as a single shift), so a Lean proof needs induction on n by hand.

usage: python3 level1.py [NMAX RMAX]      (default 8 12)
"""
import sys
M = "1RB1LA_1RC0LD_1LB0RE_0LA0LC_0RD1RF_0RB---".split("_")
T = "110"
U = T * 13 + "0" + T * 2 + "1010"
P = "10" + T + "1010"


def lo0(tape, lo):
    while tape.get(lo, 0) == 0:
        lo += 1
    return lo


def run(n, r, cap=10**7):
    start = P + U * n + T * (r + 6)
    goal = P + U * (n + 1) + T * r
    off = 0
    tape = dict(enumerate(map(int, start), off))
    pos, q = off + len(start), 4
    lo = off
    for st in range(1, cap):
        b = tape.get(pos, 0)
        tr = M[q][3 * b:3 * b + 3]
        if tr[2] == "-":
            return ("HALT", st)
        tape[pos] = int(tr[0])
        pos += 1 if tr[1] == "R" else -1
        q = ord(tr[2]) - 65
        lo = min(lo, pos)
        if q == 4 and pos - lo0(tape, lo) == len(goal):
            l = lo0(tape, lo)
            word = "".join(str(tape.get(i, 0)) for i in range(l, pos))
            if word == goal and all(v == 0 for k, v in tape.items() if k >= pos):
                return (True, st, off - l)
    return ("LONG", cap)


if __name__ == "__main__":
    nmax, rmax = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (8, 12)
    bad = 0
    for n in range(nmax + 1):
        for r in range(rmax + 1):
            res = run(n, r, cap=972 * n + 48 * r + 1014 + 1)
            bad += res != (True, 972 * n + 48 * r + 1014, 14)
    print(f"n = 0..{nmax}, r = 0..{rmax}: {(nmax + 1) * (rmax + 1)} cases, {bad} failures")
    sys.exit(1 if bad else 0)
