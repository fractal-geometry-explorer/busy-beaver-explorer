"""The run of 1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LA---_0RC1LA from blank tape, with the shared reference simulator.

usage:
  python3 py/blank.py summary STEPS          halted or not, steps, ones, the number of visited cells
  python3 py/blank.py records STEPS [K]      the tape each time the head reaches a new cell (at most K
                                             lines): "STEPS L|R hi-lo tape", as tools/c/tmrun prints it
  python3 py/blank.py dzero STEPS [K]        the tape each time D reads a 0

A halt needs D on a 0 with a 1 to its right (lean/Blank.lean, `halt_shape`), so `dzero` prints the moments the run
comes closest to it: each time D reads a 0, the cell to its right is the one that decides.  For runs of billions of
steps use the C simulator: gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun MACHINE 10000000000 records 10000.
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools", "py"))

from bbtools.machine import Machine, Run, records  # noqa: E402

M = "1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LA---_0RC1LA"
MACHINE = Machine.parse(M)
D = 3


def summary(steps):
    """(halted, steps, ones, width) of the run from blank tape, at most `steps` steps."""
    r = Run(MACHINE)
    h = r.run(steps)
    return h, r.steps, r.ones(), r.tape.hi - r.tape.lo + 1


def d_zero(steps):
    """Yield the run each time D reads a 0 (read it before advancing)."""
    r = Run(MACHINE)
    while r.steps < steps and r.step():
        if r.state == D and r.tape.get(r.head) == 0:
            yield r


def main(argv):
    cmd, steps = argv[0], int(argv[1])
    k = int(argv[2]) if len(argv) > 2 else 200
    if cmd == "summary":
        h, t, ones, w = summary(steps)
        print(f"{'halted' if h else 'running'} steps={t} ones={ones} cells={w}")
    elif cmd == "records":
        for n, (t, side, r) in enumerate(records(MACHINE, steps)):
            if n >= k:
                break
            print(t, side, r.tape.hi - r.tape.lo, r.config_str())
    elif cmd == "dzero":
        for n, r in enumerate(d_zero(steps)):
            if n >= k:
                break
            print(r.steps, r.config_str())
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
