"""The run-length frame map of 1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---1LB, with `bbtools.listframe` (tools/py/bbtools/listframe.py).

usage (from the repository root):
  python3 holdouts/1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---1LB/py/frames.py fit STEPS     fit the case table on the first STEPS steps, then check it on
                                                     the first 10 * STEPS steps (every frame at a head turn)
  python3 holdouts/1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---1LB/py/frames.py lean STEPS    fit on STEPS steps and write lean/Pieces.lean, lean/Cases.lean,
                                                     lean/Frames.lean
"""
import os
import re
import sys

M = "1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---1LB"
HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(REPO, "tools", "py"))
from bbtools.listframe import Fitter, lean_start  # noqa: E402

K = 1000000   # frames checked by native_decide in lean/Frames.lean


def main():
    if len(sys.argv) < 3 or sys.argv[1] not in ("fit", "lean"):
        sys.exit(__doc__)
    cmd, steps = sys.argv[1], int(sys.argv[2])
    F = Fitter(M)
    print("fit", F.fit(steps))
    if cmd == "fit":
        print("check on", 10 * steps, "steps (frames, mismatches, unmatched):", F.check(10 * steps))
        return
    d = os.path.join(HERE, "..", "lean")
    ns = re.search(r"namespace (\S+)", open(os.path.join(d, "Machine.lean")).read()).group(1)
    pieces, cases = F.lean(ns)
    open(os.path.join(d, "Pieces.lean"), "w").write(pieces)
    open(os.path.join(d, "Cases.lean"), "w").write(cases)
    open(os.path.join(d, "Frames.lean"), "w").write(lean_start(M, ns, K))
    print("wrote", len(F.cases), "cases to", os.path.normpath(d))


if __name__ == "__main__":
    main()
