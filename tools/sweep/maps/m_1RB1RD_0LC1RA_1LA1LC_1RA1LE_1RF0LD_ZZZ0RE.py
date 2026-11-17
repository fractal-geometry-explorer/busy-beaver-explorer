"""1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE: lean/Phases.lean (namespace H35167) `next`, `halts_iff`.

step() is a case-by-case transcription of `next` (Lean matches the cases top to bottom, and so does
step(); each branch is commented with its Lean pattern and labelled with it).  Pattern `(v + c)` becomes
`v >= c` with v bound to the value minus c.  Tags are the Lean constructor names as str.
"""
from maps._common import Stuck, bl  # noqa: F401

MACHINE = "1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE"
LEAN = "holdouts/1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE/lean/Phases.lean: next, next_sound, e_halts, init_pa, halts_iff, no_halt_phases"
VARS = ('tag', 'x|m', 'z|y|j', '-|t')
START = ('a', 0, 0)  # init_pa (0 steps)
HALT = "e(x, z) with z <= 1"
KIND = "frame"
BOUND = "1e11 phases, ~4.1e30 steps (holdouts/<m>/c/mrun.c; halt-hunt/maps logs/ph3.log)"


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
        if v0 >= 1 and v2 >= 3:  # | .q (m + 1) j (t + 3)
            m = v0 - 1
            j = v1
            t = v2 - 3
            return ('q', (_nsub(m + 1, min((m + 1), (((t + 2)) // (2))))), (j + min((m + 1), (((t + 2)) // (2)))), (_nsub(t + 3, 2 * min((m + 1), (((t + 2)) // (2)))))), 'q m+1 j t+3'
        if v0 == 0 and v2 >= 5:  # | .q 0 j (t + 5)
            j = v1
            t = v2 - 5
            return ('e', (2 * j + 4), (t + 1)), 'q 0 j t+5'
        if v0 == 0 and v2 == 4:  # | .q 0 j 4
            j = v1
            return ('a', 0, (4 * j + 9)), 'q 0 j 4'
        if v0 == 0 and v2 == 3:  # | .q 0 j 3
            j = v1
            return ('a', 0, (4 * j + 7)), 'q 0 j 3'
        if v2 == 2:  # | .q m j 2
            m = v0
            j = v1
            return ('a', m, (4 * j + 6)), 'q m j 2'
        if v2 == 1:  # | .q m j 1
            m = v0
            j = v1
            return ('a', m, (4 * j + 4)), 'q m j 1'
        if v0 >= 2 and v2 == 0:  # | .q (m + 2) j 0
            m = v0 - 2
            j = v1
            return ('q', m, 0, (4 * j + 4)), 'q m+2 j 0'
        if v0 == 1 and v2 == 0:  # | .q 1 j 0
            j = v1
            return ('e', 2, (4 * j + 2)), 'q 1 j 0'
        if v0 == 0 and v1 == 0 and v2 == 0:  # | .q 0 0 0
            return ('a', 0, 7), 'q 0 0 0'
        if v0 == 0 and v1 >= 1 and v2 == 0:  # | .q 0 (j + 1) 0
            j = v1 - 1
            return ('e', 3, (4 * j + 4)), 'q 0 j+1 0'
    if tag == 'a':
        v0, v1 = s[1:]
        if v0 >= 2:  # | .a (x + 2) y
            x = v0 - 2
            y = v1
            return ('q', x, 0, (y + 2)), 'a x+2 y'
        if v0 == 1 and v1 == 0:  # | .a 1 0
            return ('a', 0, 5), 'a 1 0'
        if v0 == 1 and v1 >= 1:  # | .a 1 (n + 1)
            n = v1 - 1
            return ('e', 2, (n + 1)), 'a 1 n+1'
        if v0 == 0 and v1 == 0:  # | .a 0 0
            return ('a', 0, 4), 'a 0 0'
        if v0 == 0 and v1 == 1:  # | .a 0 1
            return ('e', 3, 3), 'a 0 1'
        if v0 == 0 and v1 == 2:  # | .a 0 2
            return ('a', 0, 7), 'a 0 2'
        if v0 == 0 and v1 >= 3:  # | .a 0 (n + 3)
            n = v1 - 3
            return ('e', 3, (n + 1)), 'a 0 n+3'
    raise Stuck('no case of next matches %r' % (s,))


def margin(s):
    """Only at e-phases (the halting test is c <= 1 there): bits of (last component - 1)."""
    if s[0] != 'e':
        return None
    return bl(s[2] - 1)
