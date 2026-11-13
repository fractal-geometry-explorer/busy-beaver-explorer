"""Check the block laws of 1RB1LF_1RC1RB_1RD0RB_0LE0LF_---1LD_0LE1LA on a run from blank tape.

At every visit of the left end the tape is read as (01)^x0 (1)^y1 (01)^x1 (1)^y2 ... plus a short tail.  Checks
  * the sweep law: from one visit to the next, x -> x+1 and y -> y-2 (blocks of at least 7, away from the tail);
  * at each merge (a block (1)^3 about to empty) the ratio a/b of the 01-blocks on its two sides.

usage (repo root): python3 holdouts/1RB1LF_1RC1RB_1RD0RB_0LE0LF_---1LD_0LE1LA/py/analyze.py [STEPS]   (default 1e9)
"""
import os
import re
import subprocess
import sys

M = "1RB1LF_1RC1RB_1RD0RB_0LE0LF_---1LD_0LE1LA"
HERE = os.path.dirname(os.path.abspath(__file__))


def blocks(s):
    out = []
    for tok in s.split():
        tok = re.sub(r"^\[[A-F]\]", "", tok)
        if not tok:
            continue
        m = re.match(r"\((\d+)\)\^(\d+)$", tok)
        out.append((m[1], int(m[2])) if m else (tok, 1))
    return out


def pairs(b):
    xs, i = [], 0
    while i + 2 < len(b) and b[i][0] == "01" and b[i + 1][0] == "1":
        xs.append((b[i][1], b[i + 1][1]))
        i += 2
    return xs


def main():
    steps = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10**9
    exe = "/tmp/ev_" + M[:8]
    subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(HERE, "..", "c", "ev.c")], check=True)
    p = subprocess.Popen([exe, M, str(steps), "L", "*", "1", str(10**9), "12"], stdout=subprocess.PIPE, text=True)
    prev, ok, bad, visits = None, 0, 0, 0
    merges = []
    for line in p.stdout:
        head, _, tape = line.partition(": ")
        visits += 1
        xs = pairs(blocks(tape))
        if prev:
            for j in range(min(len(xs), len(prev)) - 1):
                if prev[j][1] >= 7 and prev[j][0] >= 7 and xs[j][1] >= 5:
                    if xs[j] == (prev[j][0] + 1, prev[j][1] - 2):
                        ok += 1
                    else:
                        bad += 1
        for j in range(len(xs) - 1):
            if xs[j][1] == 3 and xs[j + 1][0] >= 15:
                merges.append((xs[j][0] / xs[j + 1][0], int(head.split()[0]), j, xs[j][0], xs[j + 1][0]))
        prev = xs
    print(f"{visits} visits of the left end; sweep law held {ok} times, failed {bad} times")
    print(f"{len(merges)} merges with a right block of at least 15 pairs; smallest ratios a/b:")
    for r, k, j, a, b in sorted(merges)[:5]:
        print(f"  step {k}: block {j}, a = {a}, b = {b}, a/b = {r:.2f}")
    left = [m for m in merges if m[2] == 0]
    print(f"left-end merges: {len(left)}; ratios " + " ".join(f"{m[0]:.2f}" for m in sorted(left, key=lambda m: m[1])))


if __name__ == "__main__":
    main()
