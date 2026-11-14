"""Synthetic epochs of 1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC: what an overflow does, as a function of the reservoir.

After the overflow at step 7,545 the tape at the next visit of the right end (step 8,130) is, in run lengths,

    4 1 5 1^5 3 1^4 5 (1 3)^14 1

a prefix, a reservoir of 14 pairs (1 3) and one unit.  This script starts the plain machine (c/overflow.c) from the
same tape with k pairs instead of 14 and runs it to the next time the head leaves the tape at the left end.  k = 14 is
the machine's own run (it takes 5*10^11 steps, about 25 minutes; the other rows are configurations the machine does
not visit).  The head leaves in state C or D (it bounces and a new epoch starts) or in state E (the machine halts
on the next step): k = 8 halts.

usage: python3 overflow.py [K0 K1 [MAXSTEPS]]      rows k = K0 .. K1-1 (default 0 13), default MAXSTEPS 4e10
"""
import os, subprocess, sys, tempfile

M = "1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC"
PREFIX = [4, 1, 5, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5]
HERE = os.path.dirname(os.path.abspath(__file__))


def build():
    d = os.path.join(tempfile.gettempdir(), "ov-132695")
    os.makedirs(d, exist_ok=True)
    exe = os.path.join(d, "overflow")
    subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(HERE, "..", "c", "overflow.c")], check=True)
    return exe


def main():
    k0, k1 = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (0, 13)
    maxsteps = sys.argv[3] if len(sys.argv) > 3 else "4e10"
    exe = build()
    print("k   visits  steps  leaves in  | tape at the next visit of the right end (start)")
    for k in range(k0, k1):
        tape = PREFIX + [1, 3] * k + [1]
        out = subprocess.run([exe, M, maxsteps], input=" ".join(map(str, tape)) + "\n", capture_output=True,
                             text=True).stdout.strip()
        f = out.split()
        if f[0] != "OVERFLOW":
            print(k, out[:100]); continue
        rest = out.split("|")[1].strip()
        print(f"{k:2d} {f[2]:>8} {f[4]:>14}  {f[6]}  | " + ("HALTS" if rest.startswith("HALT") else rest[:60]), flush=True)


if __name__ == "__main__":
    main()
