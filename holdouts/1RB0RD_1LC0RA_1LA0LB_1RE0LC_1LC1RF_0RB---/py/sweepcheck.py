"""Check the outer sweep rule of 1RB0RD_1LC0RA_1LA0LB_1RE0LC_1L{C,D}1RF_0RB--- against simulation.

usage: python3 sweepcheck.py MACHINE STEPS   (builds ../c/edges from ../c/edges.c with gcc if it is missing)

At every arrival of the head at the left end of the visited region after a visit to the right end, the head is
in state C on the leftmost cell (checked).  Write the tape there as 11010 w (10)^k 1 with w a word over
c = 1101010 and a = 10 (greedy tokenisation from the left; (10)^k is the run of a's at the end).  The rule proved in lean/Rules.lean for words w with at most two
blocks (sweep0..sweep2) says: if k >= 2, the next arrival is at 11010 c w (10)^(k-1) 1, after
24*#c(w) + 4*#a(w) + 4*k + 33 steps.  This script checks that for every arrival with k >= 2 and every w, and
counts the arrivals where k < 2 (the inner phase starts there).
"""
import os
import subprocess
import sys

M, steps = sys.argv[1], sys.argv[2]
exe = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "c", "edges")
if not os.path.exists(exe):
    subprocess.run(["gcc", "-O2", "-o", exe, exe + ".c"], check=True)
out = subprocess.run([exe, M, steps, "100000000"], capture_output=True, text=True).stdout.splitlines()


def parse(t):
    """11010 w (10)^k 1 -> (nc, na, k, w) or None"""
    if not (t.startswith("11010") and t.endswith("1")):
        return None
    body = t[5:-1]
    toks, i = [], 0
    while i < len(body):
        if body.startswith("1101010", i):
            toks.append("c")
            i += 7
        elif body.startswith("10", i):
            toks.append("a")
            i += 2
        else:
            return None
    k = 0
    while toks and toks[-1] == "a":
        toks.pop()
        k += 1
    w = "".join("1101010" if x == "c" else "10" for x in toks)
    return toks.count("c"), toks.count("a"), k, w


ok = bad = short = other = 0
prev = None
for line in out:
    p = line.split()
    if len(p) < 4 or p[1] != "L":
        continue
    step, state, t = int(p[0]), p[2], p[3]
    cur = None
    if state == "C" and t.startswith(">"):
        cur = (step, parse(t[1:]))
    if prev and prev[1]:
        nc, na, k, w = prev[1]
        if k >= 2:
            want = "11010" + "1101010" + w + "10" * (k - 1) + "1"
            dt = 24 * nc + 4 * na + 4 * k + 33
            if cur and cur[1] and t[1:] == want and step - prev[0] == dt:
                ok += 1
            else:
                bad += 1
                print("MISMATCH at", prev[0])
        else:
            short += 1
    elif prev:
        other += 1
    prev = cur
print(f"{M}: {ok} sweep pairs follow the rule, {bad} mismatches, {short} arrivals with k<2 (inner phase), "
      f"{other} arrivals not of the form 11010 w (10)^k 1")
