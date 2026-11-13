"""The left-end counter of 1RB0RD_1LC1LB_---1LD_1RA0RE_1RD0LF_1LE0LD, checked on the run.

Sample: the head in state F at the left end of the visited tape.  Write the tape as words a = 10, P = 110,
Q = 100 (greedy, left to right).  It reads  F>0 0 a^n X Y W  and the first two markers run through a cycle of six
    (P, P) -> (Q, P) -> (P, Q) -> (Q, Q) -> (P, a P) -> (Q, a P) -> (P, P) ...
with n growing by 1 at each step of the cycle except the last, where it grows by 2 (so by 7 per cycle).  The rest
W changes too, mostly at its far end (each visit is one sweep over the whole tape).

usage (from the repository root):
    python3 holdouts/1RB0RD_1LC1LB_---1LD_1RA0RE_1RD0LF_1LE0LD/py/leftcounter.py STEPS
"""
import os, re, subprocess, sys, tempfile

M = "1RB0RD_1LC1LB_---1LD_1RA0RE_1RD0LF_1LE0LD"
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..")
CYCLE = [("P", "P"), ("Q", "P"), ("P", "Q"), ("Q", "Q"), ("P", "aP"), ("Q", "aP")]


def samples(steps):
    exe = os.path.join(tempfile.gettempdir(), "bbx_tmrun")
    src = os.path.join(ROOT, "tools", "c", "tmrun.c")
    if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(src):
        subprocess.run(["cc", "-O2", "-o", exe, src], check=True)
    p = subprocess.Popen([exe, M, str(steps), "at", "F", "L", str(10 ** 9)], stdout=subprocess.PIPE, text=True)
    for line in p.stdout:
        t = line.split()
        if t[0] in ("running", "halted"):
            continue
        cells = "".join(c.split("^")[0] * int(c.split("^")[1]) if "^" in c else c
                        for c in (x.split(">")[-1] for x in t[1:]))
        if not cells.startswith("00"):
            continue
        toks = re.findall(r"110|100|10|1|0", cells[2:])
        n = 0
        while n < len(toks) and toks[n] == "10":
            n += 1
        toks = toks[n:]
        x = {"110": "P", "100": "Q"}.get(toks[0], toks[0]) if toks else ""
        if len(toks) > 2 and toks[1] == "10" and toks[2] == "110":
            y, w = "aP", toks[3:]
        else:
            y, w = ({"110": "P", "100": "Q"}.get(toks[1], toks[1]) if len(toks) > 1 else ""), toks[2:]
        yield int(t[0]), n, (x, y), "".join(w)


def main(steps):
    prev, ok, bad, cyc = None, 0, 0, 0
    for s in samples(steps):
        if prev and prev[2] in CYCLE and s[2] in CYCLE:
            i = CYCLE.index(prev[2])
            good = s[2] == CYCLE[(i + 1) % 6] and s[1] == prev[1] + (2 if i == 5 else 1)
            ok += good
            bad += not good
            cyc += i == 5
            if not good and bad <= 3:
                print("mismatch:", prev[:3], "->", s[:3])
        elif prev:
            bad += 1
            if bad <= 3:
                print("not in the cycle:", prev[:3], "->", s[:3])
        prev = s
    print(f"{ok} transitions follow the cycle ({cyc} full cycles), {bad} do not; last sample n = {prev[1]}")


if __name__ == "__main__":
    main(int(sys.argv[1]))
