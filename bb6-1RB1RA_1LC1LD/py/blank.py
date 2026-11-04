"""The run of 1RB1RA_1LC1LD_1LD0LB_1RE0RF_---1RD_1RA1RB from blank tape, with the shared reference simulator.

usage:
  python3 py/blank.py summary STEPS          halted or not, steps, ones, the number of visited cells
  python3 py/blank.py records STEPS [K]      the tape each time the head reaches a new cell (at most K
                                             lines): "STEPS L|R hi-lo tape", as tools/c/tmrun prints it
  python3 py/blank.py dleft STEPS [K]        the tape each time D reads the leftmost visited cell

A halt needs D on a 0 with a 0 to its right (lean/Blank.lean, `halt_shape`); at the left end the cell to the right is
the closest the run comes to that, so `dleft` prints those moments.  For runs of billions of steps use the C simulator:
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun MACHINE 10000000000 records 10000.
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools", "py"))

from bbtools.machine import Machine, Run, records  # noqa: E402

M = "1RB1RA_1LC1LD_1LD0LB_1RE0RF_---1RD_1RA1RB"
MACHINE = Machine.parse(M)
D = 3


def summary(steps):
    """(halted, steps, ones, width) of the run from blank tape, at most `steps` steps."""
    r = Run(MACHINE)
    h = r.run(steps)
    return h, r.steps, r.ones(), r.tape.hi - r.tape.lo + 1


def d_left(steps):
    """Yield the run each time D reads the leftmost visited cell (read it before advancing)."""
    r = Run(MACHINE)
    while r.steps < steps and r.step():
        if r.state == D and r.head == r.tape.lo:
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
    elif cmd == "dleft":
        for n, r in enumerate(d_left(steps)):
            if n >= k:
                break
            print(r.steps, r.config_str())
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
