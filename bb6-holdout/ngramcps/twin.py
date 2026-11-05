"""Twin tapes: configurations NGramCPS cannot tell from the run from blank tape, and that halt.

usage: python3 twin.py OUTDIR [STEPS] [HALTSTEPS] [INDICES]   (INDICES: which twins, e.g. 0,3; default all)

For each halting round start listed in TWINS (proved to halt in Lean, see the names) and each window width n, writes
the round start as a tape file and runs tools/c/ngramtwin on it: CERTIFIED means every window of width n of the
round start occurs in the run from blank tape (where NGramCPS records it), and the round start halts, so NGramCPS
with that width fails on the machine whatever it explores first.  Also checks, as a test of the checker, that
configurations of the blank-tape run itself are covered at every width.  Writes OUTDIR/twins.tsv.
"""
import os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS = os.path.join(HERE, "..", "..", "tools", "c")
MACHINE = "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE"
MLEN = {"G": 3, "M": 2, "W": 2, "B": 3}
MCELLS = {"G": "000", "M": "11", "W": "00", "B": "111"}
MVAL = {"G": 0, "M": 1, "W": 0, "B": 1}

# (name, marks, width): round starts that halt, each the example of a Lean theorem in ../lean/thm
TWINS = [
    ("pass_r6_halt_example (R = 6)", [("W", 743), ("W", 1802), ("W", 3319)], 3326),
    ("pass_class_halt_example (R = 48)", [("W", 731), ("W", 1886), ("W", 5603)], 5652),
    ("family_open_halt (R = 178)", [("W", 1523), ("W", 2010), ("W", 2477)], 2656),
    ("lane769_far (R = 998, delta)", [("W", 449), ("W", 2462), ("W", 15193)], 16192),
]


def stripe(b, n):
    return "".join(str((b + i) % 2) for i in range(n))


def round_start(marks, W):
    """roundStart in ../lean/BB6/Marks.lean: cells from 0, the head on cell 3 in state E."""
    cells = "1000"
    prev, pos = 0, 4
    for t, p in marks:
        cells += stripe(1 - prev, p - pos) + MCELLS[t]
        prev, pos = MVAL[t], p + MLEN[t]
    cells += stripe(1 - prev, W - pos)
    return cells, 3, "E"


def write_tape(path, cells, head, state):
    with open(path, "w") as f:
        f.write(f"{state} {head}\n{cells}\n")


def check(exe, path, n, steps, hsteps):
    p = subprocess.run([exe, MACHINE, str(n), str(n), path, str(steps), str(hsteps)], capture_output=True, text=True)
    d = {}
    for line in p.stdout.splitlines():
        k, _, v = line.partition(" ")
        d.setdefault(k, v)
    return d


def main():
    out = sys.argv[1]
    steps = int(sys.argv[2]) if len(sys.argv) > 2 else 3_000_000_000
    hsteps = int(sys.argv[3]) if len(sys.argv) > 3 else 1_000_000_000
    os.makedirs(out, exist_ok=True)
    exe = os.path.join(out, "ngramtwin")
    subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(TOOLS, "ngramtwin.c")], check=True)
    pick = [int(i) for i in sys.argv[4].split(",")] if len(sys.argv) > 4 else range(len(TWINS))
    rows = []
    for name, marks, W in [TWINS[i] for i in pick]:
        cells, head, state = round_start(marks, W)
        path = os.path.join(out, "twin_%d.tape" % W)
        write_tape(path, cells, head, state)
        gaps = [b - a for a, b in zip([1] + [p for _, p in marks], [p for _, p in marks] + [W])]
        lo, hi = 1, 1200
        # the largest certified width: windows of width n are covered for every n up to some bound (a window that
        # occurs in the run contains its shorter sub-windows' occurrences too), so bisect
        res = {}
        def ok(n):
            if n not in res:
                res[n] = check(exe, path, n, steps, hsteps)
                d = res[n]
                print(name, n, d.get("verdict"), d.get("covered"), d.get("left_windows_needed"),
                      d.get("right_windows_needed"), d.get("missing", ""), flush=True)
            return res[n].get("verdict") == "CERTIFIED"
        if not ok(1):
            best = 0
        else:
            while lo < hi:
                mid = (lo + hi + 1) // 2
                if ok(mid): lo = mid
                else: hi = mid - 1
            best = lo
        rows.append((name, W, " ".join(map(str, gaps)), best, res[best]["twin_steps"] if best else "",
                     res[best]["real_steps"] if best else "", res[best]["real_width"] if best else ""))
    new = not os.path.exists(os.path.join(out, "twins.tsv"))
    with open(os.path.join(out, "twins.tsv"), "a") as f:
        if new: f.write("twin\twidth\tgaps\tlargest_certified_n\ttwin_halt_steps\tblank_run_steps\tblank_run_tape_width\n")
        for r in rows:
            f.write("\t".join(map(str, r)) + "\n")
    print(open(os.path.join(out, "twins.tsv")).read())


if __name__ == "__main__":
    main()
