"""1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE: lean/Phases.lean (namespace H70028) `next`, `halts_iff`.

step() is a case-by-case transcription of `next` (Lean matches the cases top to bottom, and so does
step(); each branch is commented with its Lean pattern and labelled with it).  Pattern `(v + c)` becomes
`v >= c` with v bound to the value minus c.  Tags are the Lean constructor names as str.
"""
from maps._common import Stuck, bl  # noqa: F401

MACHINE = "1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE"
LEAN = "holdouts/1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE/lean/Phases.lean: next, next_sound, e_halts, init_r, halts_iff, no_halt_phases"
VARS = ('tag', 'x|m', 'z|y|k', '-|t')
START = ('r', 0, 2)  # init_r
HALT = "e(x, z) with z <= 1"
KIND = "frame"
BOUND = "1e11 phases, ~4.1e30 steps (holdouts/<m>/c/mrun.c; halt-hunt/maps logs/ph4.log)"


def _nsub(a, b):
    """Lean Nat subtraction (truncated at 0)."""
    return a - b if a > b else 0


def step(s):
    tag = s[0]
    if tag == 'e':
        v0, v1 = s[1:]
        if v1 == 0:  # | .e _ 0
            return None, 'e _ 0'
        if v1 == 1:  # | .e _ 1
            return None, 'e _ 1'
        if v1 >= 2:  # | .e x (z + 2)
            x = v0
            z = v1 - 2
            return ('q', x, 0, z), 'e x z+2'
    if tag == 'q':
        v0, v1, v2 = s[1:]
        if v0 >= 1 and v2 >= 3:  # | .q (m + 1) k (t + 3)
            m = v0 - 1
            k = v1
            t = v2 - 3
            return ('q', (_nsub(m + 1, min((m + 1), (((t + 2)) // (2))))), (k + 2 * min((m + 1), (((t + 2)) // (2)))), (_nsub(t + 3, 2 * min((m + 1), (((t + 2)) // (2)))))), 'q m+1 k t+3'
        if v0 == 0 and v2 >= 5:  # | .q 0 k (t + 5)
            k = v1
            t = v2 - 5
            return ('e', (k + 4), (t + 1)), 'q 0 k t+5'
        if v0 == 0 and v2 == 4:  # | .q 0 k 4
            k = v1
            return ('r', 0, (2 * k + 8)), 'q 0 k 4'
        if v0 == 0 and v2 == 3:  # | .q 0 k 3
            k = v1
            return ('e', 1, (2 * k + 7)), 'q 0 k 3'
        if v2 == 2:  # | .q m k 2
            m = v0
            k = v1
            return ('r', m, (2 * k + 5)), 'q m k 2'
        if v0 == 0 and v2 == 1:  # | .q 0 k 1
            k = v1
            return ('e', 1, (2 * k + 4)), 'q 0 k 1'
        if v0 == 1 and v2 == 1:  # | .q 1 k 1
            k = v1
            return ('e', 3, (2 * k + 2)), 'q 1 k 1'
        if v0 >= 2 and v2 == 1:  # | .q (m + 2) k 1
            m = v0 - 2
            k = v1
            return ('q', m, 1, (2 * k + 4)), 'q m+2 k 1'
        if v0 == 0 and v2 == 0:  # | .q 0 k 0
            k = v1
            return ('e', 1, (2 * k + 2)), 'q 0 k 0'
        if v0 == 1 and v1 == 0 and v2 == 0:  # | .q 1 0 0
            return ('r', 0, 6), 'q 1 0 0'
        if v0 == 1 and v1 >= 1 and v2 == 0:  # | .q 1 (k + 1) 0
            k = v1 - 1
            return ('e', 3, (2 * k + 2)), 'q 1 k+1 0'
        if v0 >= 2 and v2 == 0:  # | .q (m + 2) k 0
            m = v0 - 2
            k = v1
            return ('q', m, 1, (2 * k + 2)), 'q m+2 k 0'
    if tag == 'r':
        v0, v1 = s[1:]
        if v0 == 0 and v1 == 0:  # | .r 0 0
            return ('e', 1, 1), 'r 0 0'
        if v0 == 0 and v1 >= 1:  # | .r 0 (y + 1)
            y = v1 - 1
            return ('e', 1, (y + 2)), 'r 0 y+1'
        if v0 == 1 and v1 == 0:  # | .r 1 0
            return ('e', 1, 5), 'r 1 0'
        if v0 == 1 and v1 == 1:  # | .r 1 1
            return ('r', 0, 6), 'r 1 1'
        if v0 == 1 and v1 == 2:  # | .r 1 2
            return ('e', 3, 1), 'r 1 2'
        if v0 == 1 and v1 >= 3:  # | .r 1 (y + 3)
            y = v1 - 3
            return ('e', 3, (y + 2)), 'r 1 y+3'
        if v0 >= 2 and v1 == 0:  # | .r (x + 2) 0
            x = v0 - 2
            return ('q', x, 1, 1), 'r x+2 0'
        if v0 >= 2 and v1 >= 1:  # | .r (x + 2) (y + 1)
            x = v0 - 2
            y = v1 - 1
            return ('q', x, 1, (y + 2)), 'r x+2 y+1'
    raise Stuck('no case of next matches %r' % (s,))


def margin(s):
    """Only at e-phases (the halting test is c <= 1 there): bits of (last component - 1)."""
    if s[0] != 'e':
        return None
    return bl(s[2] - 1)
