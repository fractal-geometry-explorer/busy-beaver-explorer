"""1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD: lean/Phases.lean (namespace H149707) `next`, `halts_iff`.

step() is a case-by-case transcription of `next` (Lean matches the cases top to bottom, and so does
step(); each branch is commented with its Lean pattern and labelled with it).  Pattern `(v + c)` becomes
`v >= c` with v bound to the value minus c.  Tags are the Lean constructor names as str.
"""
from maps._common import Stuck, bl  # noqa: F401

MACHINE = "1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD"
LEAN = "holdouts/1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD/lean/Phases.lean: next, next_sound, ps_halts, init_ps, halts_iff, no_halt_phases"
VARS = ('tag', 'a|R', 'c|m', '-|c')
START = ('ps', 0, 2)  # init_ps
HALT = "ps(a, c) with c <= 1"
KIND = "frame"
BOUND = "1e11 phases, 2e10 pass starts (holdouts/<m>/c/psq.c; halt-hunt/maps logs/psq.log)"


def _nsub(a, b):
    """Lean Nat subtraction (truncated at 0)."""
    return a - b if a > b else 0


def step(s):
    tag = s[0]
    if tag == 'ps':
        v0, v1 = s[1:]
        if v1 == 0:  # | .ps _ 0
            return None, 'ps _ 0'
        if v1 == 1:  # | .ps _ 1
            return None, 'ps _ 1'
        if v0 == 0 and v1 == 2:  # | .ps 0 2
            return ('ps', 0, 5), 'ps 0 2'
        if v0 == 0 and v1 >= 3:  # | .ps 0 (c + 3)
            c = v1 - 3
            return ('ps', 2, (c + 1)), 'ps 0 c+3'
        if v0 >= 1 and v1 >= 2:  # | .ps (a + 1) (c + 2)
            a = v0 - 1
            c = v1 - 2
            return ('q', a, 2, (c + 2)), 'ps a+1 c+2'
    if tag == 'q':
        v0, v1, v2 = s[1:]
        if v0 >= 1 and v1 >= 2 and v2 >= 3:  # | .q (R + 1) (m + 2) (c + 3)
            R = v0 - 1
            m = v1 - 2
            c = v2 - 3
            return ('q', (_nsub(R + 1, min((R + 1), (((c + 2)) // (2))))), (m + 2 + 2 * min((R + 1), (((c + 2)) // (2)))), (_nsub(c + 3, 2 * min((R + 1), (((c + 2)) // (2)))))), 'q R+1 m+2 c+3'
        if v0 == 0 and v1 >= 2 and v2 >= 5:  # | .q 0 (m + 2) (c + 5)
            m = v1 - 2
            c = v2 - 5
            return ('ps', (m + 4), (c + 1)), 'q 0 m+2 c+5'
        if v0 == 0 and v1 >= 2 and v2 == 1:  # | .q 0 (m + 2) 1
            m = v1 - 2
            return ('ps', 0, (2 * m + 8)), 'q 0 m+2 1'
        if v0 == 0 and v1 >= 2 and v2 == 2:  # | .q 0 (m + 2) 2
            m = v1 - 2
            return ('ps', 0, (2 * m + 6)), 'q 0 m+2 2'
        if v0 == 0 and v1 >= 2 and v2 == 3:  # | .q 0 (m + 2) 3
            m = v1 - 2
            return ('ps', 0, (2 * m + 11)), 'q 0 m+2 3'
        if v0 == 0 and v1 >= 2 and v2 == 4:  # | .q 0 (m + 2) 4
            m = v1 - 2
            return ('ps', 0, (2 * m + 9)), 'q 0 m+2 4'
        if v0 == 1 and v1 >= 2 and v2 == 1:  # | .q 1 (m + 2) 1
            m = v1 - 2
            return ('ps', 2, (2 * m + 6)), 'q 1 m+2 1'
        if v0 == 1 and v1 >= 2 and v2 == 2:  # | .q 1 (m + 2) 2
            m = v1 - 2
            return ('ps', 2, (2 * m + 4)), 'q 1 m+2 2'
        if v0 >= 2 and v1 >= 2 and v2 == 1:  # | .q (R + 2) (m + 2) 1
            R = v0 - 2
            m = v1 - 2
            return ('q', R, 2, (2 * m + 8)), 'q R+2 m+2 1'
        if v0 >= 2 and v1 >= 2 and v2 == 2:  # | .q (R + 2) (m + 2) 2
            R = v0 - 2
            m = v1 - 2
            return ('q', R, 2, (2 * m + 6)), 'q R+2 m+2 2'
        if True:  # | .q _ _ _
            raise Stuck('next is none at %r (never reached per next_some; not a halting case)' % (s,))
    raise Stuck('no case of next matches %r' % (s,))


def margin(s):
    """Only at ps-phases (the halting test is c <= 1 there): bits of (last component - 1)."""
    if s[0] != 'ps':
        return None
    return bl(s[2] - 1)
