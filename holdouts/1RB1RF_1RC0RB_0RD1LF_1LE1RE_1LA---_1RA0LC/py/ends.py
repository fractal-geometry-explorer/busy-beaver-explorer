"""How far back the chain ends of 1RB1RF_1RC0RB_0RD1LF_1LE1RE_1LA---_1RA0LC read, checked on the run.

Sample as in py/chains.py (the head in A at the right end, on a 0).  The tape is a list of pair runs (10)^x separated
by short markers, ending in a block of ones.  For each pair of consecutive samples this script finds the leftmost
cell the head visited in between (c/ev.c), and reports which run it lies in, counted from the right (0: right of all
runs, inside the final ones), or that the head reached the left end of the tape.  It also prints the first sample with
r runs, for each r.  This is the measurement behind the README section "Chain ends": a map on a fixed number of
runs (a finite frame map) cannot cover the run, because the number of runs grows and some transitions read the
whole tape.

usage (from the repository root):
    python3 holdouts/1RB1RF_1RC0RB_0RD1LF_1LE1RE_1LA---_1RA0LC/py/ends.py STEPS
"""
import collections, os, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))


def runs(s):
    """start and length (in cells) of each maximal (10)^x run with x >= 1, left to right (greedy)."""
    out, i = [], 0
    while i < len(s):
        m = re.match(r"(?:10)+", s[i:])
        if m:
            out.append((i, len(m.group(0)))); i += len(m.group(0))
        else:
            i += 1
    return out


def main(steps):
    exe = os.path.join(tempfile.gettempdir(), "bbx_m11_ev")
    subprocess.run(["cc", "-O2", "-o", exe, os.path.join(HERE, "..", "c", "ev.c")], check=True)
    out = subprocess.run([exe, str(steps)], capture_output=True, text=True, check=True).stdout.split("\n")
    ev = [l.split() for l in out if l and not l.startswith("HALT")]
    cnt = collections.Counter()
    for (_, _, s0), (_, mn, _) in zip(ev, ev[1:]):
        mn = int(mn)
        if mn <= 0:
            cnt["reaches the left end of the tape"] += 1
            continue
        rs = runs(s0)
        after = [j for j, (st, ln) in enumerate(rs) if st + ln > mn]
        cnt[f"reads into run {len(rs) - after[0] if after else 0} from the right"] += 1
    print(f"{len(ev)} samples, {len(ev) - 1} transitions")
    for k in sorted(cnt):
        print(f"  {cnt[k]:6d}  {k}")
    first = {}
    for st, _, s in ev:
        first.setdefault(len(runs(s)), int(st))
    print("first sample with r runs:", ", ".join(f"r={r} at step {first[r]:,}" for r in sorted(first)))


if __name__ == "__main__":
    main(int(sys.argv[1]))
