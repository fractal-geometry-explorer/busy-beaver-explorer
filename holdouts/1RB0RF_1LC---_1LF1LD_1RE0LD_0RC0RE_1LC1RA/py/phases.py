"""The half-phases of 1RB0RF_1LC---_1LF1LD_1RE0LD_0RC0RE_1LC1RA from blank tape, with the macro simulator.

At the end of each half-phase the tape is a short word w at the left end followed by k copies of `10` (head in F at
the right end) or of `01` (head in A at the right end).  Prints the step, w, the word, k, and c = k - 3k_prev/2.

usage: python3 phases.py [STEPS]      (default 1e11; 7.6e13 takes about three minutes)
"""
import os
import re
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "tools", "py"))
from bbtools.macro import MacroRun  # noqa: E402

M = "1RB0RF_1LC---_1LF1LD_1RE0LD_0RC0RE_1LC1RA"
PAT = re.compile(r"^(.*?)\s*\((10|01)\)\^(\d+)$")


def left_word(r):
    toks = []
    for w, c in r.runs()[0]:
        toks.append(w * c if len(set(w)) > 1 and c < 4 else (f"({w})^{c}" if len(set(w)) > 1 else w[0] * (len(w) * c)))
    return toks


def main(argv):
    steps = int(float(argv[0])) if argv else int(1e11)
    r = MacroRun(M, 2)
    was, prev = False, None
    while r.steps < steps:
        if not r.step():
            print("halts after", r.steps, "steps")
            return
        at = len(r.right) == 1 and r.dir == 1 and r.state in (0, 1, 4, 5)
        if at and not was:
            lw = r.runs()[0]
            big = [i for i, (w, c) in enumerate(lw) if len(set(w)) > 1 and c >= 4]
            if big and sum(len(w) * c for w, c in lw[big[-1] + 1:]) <= 4:
                i = big[-1]
                word, k = lw[i]
                rest = "".join(w * c for w, c in lw[:i])
                tail = "".join(w * c for w, c in lw[i + 1:])
                if tail == word[0]:          # w (01)^k 0 = w 0 (10)^k  (block alignment)
                    rest, word, tail = rest + tail, word[::-1], ""
                if tail in ("", "11") and not (prev is not None and k <= prev):
                    c = "" if prev is None else f"  c = {k - 1.5 * prev:+g}"
                    print(f"{r.steps} w={rest!r} ({word})^{k}{c}", flush=True)
                    prev = k
        was = at


if __name__ == "__main__":
    main(sys.argv[1:])
