"""Check the queue law of 1RB1RA_1RC---_1RD0LD_1LE1RF_0RA1LD_0RC0LC on a run from blank tape.

At every visit of the left end the tape is a row of blocks 1^n separated by `0 0 1 0 0`, plus a short tail where new
blocks are made.  From one visit to the next the first block disappears, the second becomes the first with 8 more
ones, and every other block gains 6 ones.  Prints the number of checks, failures, and the queue length over time.

usage (repo root): python3 holdouts/1RB1RA_1RC---_1RD0LD_1LE1RF_0RA1LD_0RC0LC/py/queue.py [STEPS]   (default 1e9)
"""
import os
import re
import subprocess
import sys

M = "1RB1RA_1RC---_1RD0LD_1LE1RF_0RA1LD_0RC0LC"
HERE = os.path.dirname(os.path.abspath(__file__))


def blocks(tape):
    s = re.sub(r"\[[A-F]\]", "", tape).strip()
    vals = []
    for p in s.split(" 0 0 1 0 0 "):
        p = p.strip()
        m = re.fullmatch(r"0?\s*\(1\)\^(\d+)", p)
        if m:
            vals.append(int(m[1]))
            continue
        m = re.fullmatch(r"0?\s*((?:1 ){0,2}1)", p)
        if not m:
            break
        vals.append(m[1].count("1"))
    return vals


def main():
    steps = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10**9
    exe = "/tmp/ev_" + M[:8]
    subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(HERE, "..", "c", "ev.c")], check=True)
    p = subprocess.Popen([exe, M, str(steps), "L", "*", "1", str(10**9), "12"], stdout=subprocess.PIPE, text=True)
    prev, ok, bad, n = None, 0, 0, 0
    for line in p.stdout:
        head, _, tape = line.partition(": ")
        v = blocks(tape)
        n += 1
        if prev and len(prev) > 4:
            if v[0] == prev[1] + 8:
                ok += 1
            else:
                bad += 1
            for i in range(2, min(len(prev), len(v) + 1) - 3):
                if v[i - 1] == prev[i] + 6:
                    ok += 1
                else:
                    bad += 1
        if n % 250 == 0:
            print(f"step {head.split()[0]}: {len(v)} blocks, first {v[0] if v else None}")
        prev = v
    print(f"{n} visits of the left end; queue law held {ok} times, failed {bad} times")


if __name__ == "__main__":
    main()
