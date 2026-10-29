"""Look at a run from blank tape, for finding its macro structure.

usage:
  python3 -m bbtools.explore records MACHINE STEPS [K]        the tape each time the head reaches a new cell
  python3 -m bbtools.explore events MACHINE STEPS STATE SIDE  the tape each time the head, in STATE, is at the left
                                                             (SIDE L) or right (SIDE R) end of the visited cells
  python3 -m bbtools.explore blocks MACHINE STEPS STATE SIDE  the same events as lists of block lengths: the tape
                                                             between the ends split at runs of 0s, "ones-run:zeros-run"

Tapes are printed run-length coded (`1^5 0 C>1 1^2`, the head in state C on the cell after `>`).  For runs of
billions of steps use tools/c/tmrun (same output format for `records`).
"""
import sys

from .machine import Machine, Run, STATES, rle_cells


def events(m, steps, state, side):
    r = Run(m)
    while r.steps < steps:
        if not r.step():
            yield r, True
            return
        if r.state == state and ((side == "L" and r.head == r.tape.lo) or (side == "R" and r.head == r.tape.hi)):
            yield r, False


def blocks(cells):
    """[(ones, zeros), ...] for the cells, which start at a 1 or a 0 (then the first entry has ones = 0)."""
    out, i = [], 0
    while i < len(cells):
        j = i
        while j < len(cells) and cells[j] == 1:
            j += 1
        k = j
        while k < len(cells) and cells[k] == 0:
            k += 1
        out.append((j - i, k - j))
        i = k
    return out


def main(argv):
    cmd, m, steps = argv[0], Machine.parse(argv[1]), int(argv[2])
    if cmd == "records":
        from .machine import records
        k = int(argv[3]) if len(argv) > 3 else 200
        for n, (t, side, r) in enumerate(records(m, steps)):
            if n >= k:
                break
            print(t, side, r.tape.hi - r.tape.lo, r.config_str())
    elif cmd in ("events", "blocks"):
        st, side = STATES.index(argv[3]), argv[4]
        for r, halted in events(m, steps, st, side):
            if halted:
                print(r.steps, "HALT", r.config_str())
                break
            if cmd == "events":
                print(r.steps, r.config_str())
            else:
                print(r.steps, " ".join(f"{a}:{b}" for a, b in blocks(r.tape.word())))
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
