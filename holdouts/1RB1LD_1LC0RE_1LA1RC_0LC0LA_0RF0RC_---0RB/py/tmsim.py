"""A plain simulator started from a given finite tape (cells as a list, the rest blank), for the overflow
experiments: run until the head, in a given state, is on the leftmost visited cell reading a given symbol."""
import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../../tools/py'))
from bbtools.machine import Machine  # noqa: E402

STATES = "ABCDEF"


def run_to_event(m, cells, head, state, ev_state, ev_read, max_steps):
    """Run from `cells` (head at index `head`, in `state`) until the head is in `ev_state` on the leftmost cell
    visited so far (counting the start cell as the left end) and reads `ev_read`. Returns (steps, cells, head index)
    with the cells from the left end; steps is None on a halt and -1 when max_steps is reached."""
    tape = {i: c for i, c in enumerate(cells)}
    h, q, n, lo, hi = head, STATES.index(state), 0, head, max(len(cells) - 1, head)
    eq = STATES.index(ev_state)
    tab = m.table
    res = -1
    while n < max_steps:
        y = tape.get(h, 0)
        tr = tab[q][y]
        if tr is None:
            res = None
            break
        w, d, q = tr
        tape[h] = w
        h += d
        n += 1
        if h < lo:
            lo = h
        if h > hi:
            hi = h
        if q == eq and h == lo and tape.get(h, 0) == ev_read:
            res = n
            break
    out = [tape.get(i, 0) for i in range(lo, hi + 1)]
    return res, out, h - lo
