"""The phase map of 1RB0RE_1RC0RF_1LD1RA_1LB1LD_1RA1LB_---0LD on (gap, tail), from direct simulation of single phases.

A phase starts at `0^inf B> 0 1 0^X T` (X = the gap, T = the tail, a finite word) and ends at the next such
configuration with a larger gap X'.  `c/phase.c` simulates one phase cell by cell.  Experimentally the outcome
depends on X only through X mod 4:  X' = (3X + d)/2 and T', with (d, T') a function of (X mod 4, T).  `entry`
tabulates this function lazily: it runs four phases with X in [200, 330) in the residue class and checks that
d and T' agree.  This is a measured table, not a proof (Lean has the first part of a phase: `lean/Phase.lean`).

usage: python3 tailmap.py orbit N    iterate N phases from the blank-tape orbit (start X = 6, T = 1^8), exact big
                                     integers for X; reports a halt if a table entry halts
       python3 tailmap.py near N     the same, and counts the phases where another residue of X mod 4 would halt
"""
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
EXE = os.path.join(tempfile.gettempdir(), f"m1phase_{os.getuid()}")


def rl(T):
    return " ".join(f"{m.group()[0]}^{len(m.group())}" for m in re.finditer(r"1+|0+", T))


def run(cases):
    if not os.path.exists(EXE):
        subprocess.run(["gcc", "-O2", "-o", EXE, os.path.join(HERE, "..", "c", "phase.c")], check=True)
    inp = "".join(f"{X} {T or '-'}\n" for X, T in cases)
    out = subprocess.run([EXE], input=inp, capture_output=True, text=True).stdout.strip().split("\n")
    return [tuple(line.split()) for line in out]


def entry(T, res, cache={}):
    key = (T, res)
    if key not in cache:
        Xs = [X for X in range(200, 330) if X % 4 == res][:4]
        vals = set()
        for X, o in zip(Xs, run([(X, T) for X in Xs])):
            vals.add(o if len(o) != 3 else (int(o[1]) * 2 - 3 * X, o[2]))
        cache[key] = vals.pop() if len(vals) == 1 else ("IRREG", vals)
    return cache[key]


def orbit(n, near=False):
    X, T = 6, "11111111"
    seq = [(X, T)]
    while X < 330:  # the first phases directly
        o = run([(X, T)])[0]
        X, T = int(o[1]), o[2]
        seq.append((X, T))
    direct = len(seq) - 1
    res, would_halt, alts = [0] * 4, 0, 0
    for i in range(n):
        e = entry(T, X % 4)
        if e[0] in ("HALT", "LONG", "IRREG"):
            print("stops at phase", len(seq), "X mod 4 =", X % 4, "tail", rl(T), e)
            break
        if near:
            for r in range(4):
                if r != X % 4:
                    alts += 1
                    would_halt += entry(T, r)[0] == "HALT"
        res[X % 4] += 1
        X = (3 * X + e[0]) >> 1
        T = e[1]
        if len(seq) < 45:
            seq.append((X, T))
    for x, t in seq:
        print(x, rl(t))
    print(f"... {direct} phases simulated directly, then {i + 1} phases by the table, no halt; "
          f"X has {X.bit_length()} bits, the tail {len(T)} cells in {len(rl(T).split())} blocks")
    print("X mod 4 along the table phases:", res)
    if near:
        print(f"other residues tried: {alts}, of which halting: {would_halt}")


if __name__ == "__main__":
    orbit(int(sys.argv[2]), near=sys.argv[1] == "near")
