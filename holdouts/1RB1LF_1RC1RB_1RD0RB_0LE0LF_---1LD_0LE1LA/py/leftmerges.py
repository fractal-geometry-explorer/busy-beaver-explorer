"""Merges at the left end of 1RB1LF_1RC1RB_1RD0RB_0LE0LF_---1LD_0LE1LA, from the block machine (c/msim.c).

The machine can only halt at a merge at the left end whose right block is not shorter than the left one (Lean:
`left_merge_halts`).  This runs the block machine (the C twin of lean/Macro.lean) from blank tape and prints, at every
merge at the left end, the left block X0, the right block X1, the block after it X2 (pairs of cells) and

  X1/X0           must stay below 1 (about) for the machine not to halt at this merge;
  (X0-X1)/X2      above 1 makes the *next* left-end merge safe too: from one left-end merge to the next, X0 - X1 does
                  not decrease (both blocks gain a pair per sweep, and merges further right only shorten X1), and right
                  after the merge the new left block is X0 - X1 and the new right block is X2.

usage (repo root): python3 holdouts/1RB1LF_1RC1RB_1RD0RB_0LE0LF_---1LD_0LE1LA/py/leftmerges.py [STEPS]   (default 1e15)
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def main():
    steps = sys.argv[1] if len(sys.argv) > 1 else "1e15"
    exe = "/tmp/msim_60424"
    subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(HERE, "..", "c", "msim.c")], check=True)
    out = subprocess.run([exe, steps, "0", "tapes"], check=True, capture_output=True, text=True).stdout.splitlines()
    rows = []
    for i, line in enumerate(out):
        if line.startswith("HALT"):
            print(line)
        if not line.startswith("LEFTMERGE"):
            continue
        f = dict(kv.split("=") for kv in line.split()[1:])
        runs = [(t.split("^")[0], int(t.split("^")[1])) for t in out[i + 1].split()[1:]]
        xs = [c for w, c in runs if w in ("01", "10")]
        rows.append((int(f["steps"]), xs[0], xs[1], xs[2] if len(xs) > 2 else 0, len(xs)))
    print(f"{'step':>22} {'X0':>12} {'X1':>12} {'X2':>11} {'X1/X0':>6} {'(X0-X1)/X2':>10} blocks")
    for s, x0, x1, x2, nb in rows:
        r2 = f"{(x0 - x1) / x2:10.2f}" if x2 else " " * 10
        print(f"{s:>22,} {x0:>12,} {x1:>12,} {x2:>11,} {x1 / x0:6.3f} {r2} {nb:>4}")
    big = [r for r in rows if r[1] >= 100]
    print(f"{len(rows)} merges at the left end; with X0 >= 100: X1/X0 between {min(r[2] / r[1] for r in big):.3f} and "
          f"{max(r[2] / r[1] for r in big):.3f}, (X0-X1)/X2 at least {min((r[1] - r[2]) / r[3] for r in big if r[3]):.2f}")
    print(out[-1])


if __name__ == "__main__":
    main()
