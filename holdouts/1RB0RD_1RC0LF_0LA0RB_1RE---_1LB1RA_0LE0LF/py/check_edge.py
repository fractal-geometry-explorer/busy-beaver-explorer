"""Check c/edge.c against the plain machine, and measure the periods of the data prefixes.

usage: python3 check_edge.py [STEPS]     (default 3,000,000 plain steps; needs gcc)

1. Runs the machine step by step from blank tape and lists every moment the configuration is Z(n, R):
   tape 0^inf (1001111)^n 0100 111111 01 | R, head on the first cell of R (cell 13) in state E.
   Compares step count, n and R with the lines printed by edge.c (which jumps over the wall): they must agree.
2. From 300,000 cycles of edge.c: for k = 1..120 the period of the first k data cells as a function of the cycle
   number (after cycle 50,000), and whether the next prefix is a function of the prefix.
"""
import os
import re
import subprocess
import sys
import tempfile
from collections import defaultdict

M = "1RB0RD_1RC0LF_0LA0RB_1RE---_1LB1RA_0LE0LF"
HERE = os.path.dirname(os.path.abspath(__file__))


def plain(steps):
    tr = {}
    for s in range(6):
        for r in range(2):
            t = M[s * 7 + r * 3:s * 7 + r * 3 + 3]
            tr[(s, r)] = None if t[0] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
    tape = defaultdict(int)
    pos = st = lo = hi = 0
    out = []
    for i in range(1, steps + 1):
        w, d, q = tr[(st, tape[pos])]
        tape[pos] = w
        pos += d
        st = q
        lo, hi = min(lo, pos), max(hi, pos)
        if st == 4 and d == 1 and pos == 13:
            left = ''.join(str(tape[p]) for p in range(lo, pos))
            mm = re.fullmatch(r'0*((?:1001111)+)010011111101', left)
            if mm:
                out.append((i, len(mm.group(1)) // 7, ''.join(str(tape[p]) for p in range(pos, hi + 1))))
    return out


def edge(exe, cycles):
    res = subprocess.run([exe, str(cycles), "1", "x"], capture_output=True, text=True, check=True).stdout
    rows = []
    for line in res.splitlines():
        p = line.split()
        if p[0] in ("grow", "cycle"):
            rows.append((int(p[5]), int(p[3]), p[10].rstrip('0'), int(p[9])))
    return rows


def main():
    steps = int(sys.argv[1]) if len(sys.argv) > 1 else 3_000_000
    with tempfile.TemporaryDirectory() as tmp:
        exe = os.path.join(tmp, "edge")
        subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(HERE, "..", "c", "edge.c")], check=True)
        zs = plain(steps)
        assert zs[0][:2] == (2035, 7), zs[0]
        es = edge(exe, len(zs) - 1)
        for (i, n, r), (ei, en, er, _) in zip(zs[1:], es):
            assert (i, n, r.rstrip('0')) == (ei, en, er), (i, n, r, ei, en, er)
        print(f"plain machine and edge.c agree on {len(zs) - 1} cycles (to step {zs[-1][0]:,}, n = {zs[-1][1]})")
        rows = edge(exe, 300_000)
    data = [r[2] for r in rows]
    start = 50_000
    last = None
    print("cells  distinct prefixes  period  next prefix a function of the prefix")
    for k in range(1, 121):
        seq = [d[:k].ljust(k, '0') for d in data[start:]]
        per = next((p for p in range(1, 100_000) if all(seq[i] == seq[i + p] for i in range(len(seq) - p))), None)
        nxt = {}
        fun = all(nxt.setdefault(a, b) == b for a, b in zip(seq, seq[1:]))
        if per != last:
            print(f"{k:5d}  {len(set(seq)):17d}  {per}  {'yes' if fun else 'no'}")
            last = per


if __name__ == "__main__":
    main()
