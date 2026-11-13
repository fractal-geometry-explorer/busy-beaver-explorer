"""Run one machine of the 40-machine family far with the exact block-list map and write data/f05_run.json.

Every machine of frames.FAMILY is run as its frame-A conjugate from the frame-A start state (frames.py), with
hybrid.py (clean visits by the closed form, a Lean theorem; every other visit by the exact run-length simulator,
memoised), or hybrid2.py for the three machines whose F-event leaves the block-list shape (D1 = 1LF, F0 = 0LD).
With `check`, the F-events (step and the cell F reads) of the first CHECK steps are compared with the plain
cell-by-cell simulator c/family.c (compiled to ./family in the current directory, or $FAMILY_BIN).

The summary holds: the step count reached, the left-end events (the first 80 with their block lists, then only
their number), the F-events and the tape around the head at each (as a count per context), and the *drift* figures:
at a left-end event with blocks [b1, ..., bk] the drifts are b(i+1) - 5 b(i) for 2 <= i <= k-2 (neither the first
nor the last block); `visit_conserves` (lean/Family.lean) proves that clean visits do not change them.

usage: python3 f05_run.py MACHINE STEPS [check [CHECK=3e9]]
"""
import collections
import json
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
HOLD = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import frames  # noqa: E402
import hybrid  # noqa: E402
import hybrid2  # noqa: E402

KEEP = 80


def needs_raw(fa):
    """D1 = 1LF with F0 = 0LD: the F-event leaves a gadget `0 1` between two blocks."""
    return fa.split("_")[3][3:] == "1LF" and fa.split("_")[5][:3] == "0LD"


def run(machine, N):
    fr, fa, st = frames.info(machine)
    h = (hybrid2.Hybrid2 if needs_raw(fa) else hybrid.Hybrid)(fa)
    t0 = time.time()
    r = h.run(ord(st) - 65, N)
    return h, r, time.time() - t0


def drifts(l):
    return [l[i + 1] - 5 * l[i] for i in range(1, len(l) - 2)]


def summary(machine, target, steps, halted, top, fev, secs, stats):
    """top: [(step, pos, list)], fev: [(step, cell read, context)]"""
    fr, fa, st = frames.info(machine)
    ctx = collections.Counter((y, c) for (_, y, c) in fev)
    prev = set()
    late = []          # (step, smallest |drift| in the list, smallest |drift| not there at the event before)
    for (t, p, l) in top:
        d = drifts(l)
        new = [abs(x) for x in d if x not in prev]
        prev = set(d)
        if d:
            late.append((t, min(abs(x) for x in d), min(new) if new else None))
    def after(k, j):
        v = [x[j] for x in late if x[0] >= 10 ** k and x[j] is not None]
        return str(min(v)) if v else None
    return {
        "machine": machine, "frame": fr, "frame_a": fa, "start": st,
        "simulator": "hybrid2.py" if needs_raw(fa) else "hybrid.py",
        "target_steps": target, "steps": str(steps), "steps_digits": len(str(steps)),
        "halted": halted, "seconds": round(secs),
        "left_end_events": len(top), "blocks_at_end": len(top[-1][2]) if top else 0,
        "f_events": len(fev), "f_reads_one": sum(1 for f in fev if f[1] == 1),
        "f_contexts": [{"reads": y, "context": c, "count": n} for (y, c), n in ctx.most_common()],
        "f_steps_first": [str(f[0]) for f in fev[:12]],
        "drift": {"smallest_after_1e20": after(20, 1), "smallest_after_1e100": after(100, 1),
                  "smallest_new_after_1e20": after(20, 2), "smallest_new_after_1e50": after(50, 2),
                  "smallest_new_after_1e100": after(100, 2)},
        "stats": stats,
        "left_end": [{"step": str(t), "pos": p, "blocks": [str(x) for x in l]} for (t, p, l) in top[:KEEP]],
        "last_left_end": {"step": str(top[-1][0]), "pos": top[-1][1],
                          "first_blocks": [str(x) for x in top[-1][2][:6]]} if top else None,
    }


def check(machine, M):
    """F-events of the plain simulator in the first M steps: [(step, cell read)]"""
    fr, fa, st = frames.info(machine)
    exe = os.environ.get("FAMILY_BIN", "./family")
    out = subprocess.run([exe, "enter", fa + ":" + st, str(int(M)), "F"], capture_output=True, text=True).stdout
    ev = []
    for line in out.split("\n"):
        if line and line[0].isdigit():
            ev.append((int(line.split()[0]), int(line.split("[F]")[1][0])))
        elif line.startswith("HALT"):
            ev.append(("halt", int(line.split()[1])))
    return ev


def main(argv):
    m, target = argv[0], argv[1]
    h, r, secs = run(m, float(target))
    s = summary(m, target, h.sim.steps, h.halted, h.top, h.fev, secs, h.stats)
    path = os.path.join(HOLD, m, "data", "f05_run.json")
    old = json.load(open(path)) if os.path.exists(path) else {}
    if len(argv) > 2 and argv[2] == "check":
        M = float(argv[3]) if len(argv) > 3 else 3e9
        a = check(m, M)
        b = [(f[0], f[1]) for f in h.fev if f[0] <= M]
        s["validated"] = {"direct_steps": "%.0e" % M, "f_events": len(a), "match": a == b}
    elif "validated" in old:
        s["validated"] = old["validated"]
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as f:
        json.dump(s, f, indent=0)
        f.write("\n")
    print(m, "steps 1e%d" % (s["steps_digits"] - 1), "HALT" if h.halted else "no halt", "left-end", len(h.top),
          "F", len(h.fev), "F reads 1:", s["f_reads_one"], s.get("validated"), f"{secs:.0f}s")


if __name__ == "__main__":
    main(sys.argv[1:])
