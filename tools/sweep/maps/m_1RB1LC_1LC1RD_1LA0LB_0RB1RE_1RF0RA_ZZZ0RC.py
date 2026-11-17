"""1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC: lean/Phases.lean (namespace H8084) `next`, `halts_iff`.

step() is a case-by-case transcription of `next` (Lean matches the cases top to bottom, and so does
step(); each branch is commented with its Lean pattern and labelled with it).  Pattern `(v + c)` becomes
`v >= c` with v bound to the value minus c.  Tags are the Lean constructor names as str.
"""
from maps._common import Stuck, bl  # noqa: F401
from maps._cycle import cycle_accel

MACHINE = "1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC"
LEAN = "holdouts/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC/lean/Phases.lean: next, next_sound, none_halts, init_start, halts_iff, no_halt_phases"
VARS = ('tag', 'l', 'j', 'r?')
START = ('e', 1, 0)  # init_start (1 step)
HALT = "next is none: b(l,j,2), d(l,0,1), d(l,1,0)"
KIND = "frame"
BOUND = "1e11 frames, no halt (this module's exact accel, tools/sweep group D run, 2026-11-17); before: 1e8 frames (Lean no_halt_phases, native_decide, ~5.95e11 steps), 1e15 steps (c/mrun.c macro sim)"


def step(s):
    tag = s[0]
    if tag == 'b':
        v0, v1, v2 = s[1:]
        if v2 == 0:  # | .b l j 0
            l = v0
            j = v1
            return ('e', (l), (j + 1)), 'b l j 0'
        if v2 == 1:  # | .b l j 1
            l = v0
            j = v1
            return ('e', (l), (j + 2)), 'b l j 1'
        if v2 == 2:  # | .b l j 2
            l = v0
            j = v1
            return None, 'b l j 2'
        if v2 == 3:  # | .b l j 3
            l = v0
            j = v1
            return ('f', (l), (j + 1)), 'b l j 3'
        if v2 >= 4:  # | .b l j (r + 4)
            l = v0
            j = v1
            r = v2 - 4
            return ('a', (l), (j + 1), (r + 1)), 'b l j r+4'
    if tag == 'a':
        v0, v1, v2 = s[1:]
        if v2 == 0:  # | .a l j 0
            l = v0
            j = v1
            return ('f', (l), (j)), 'a l j 0'
        if v0 == 0 and v2 >= 1:  # | .a 0 j (r + 1)
            j = v1
            r = v2 - 1
            return ('d', (0), (j + 1), (r + 3)), 'a 0 j r+1'
        if v0 >= 1 and v2 >= 1:  # | .a (l + 1) j (r + 1)
            l = v0 - 1
            j = v1
            r = v2 - 1
            return ('b', (l), (j), (r + 3)), 'a l+1 j r+1'
    if tag == 'c':
        v0, v1, v2 = s[1:]
        if v1 == 0:  # | .c l 0 r
            l = v0
            r = v2
            return ('d', (l), (0), (r)), 'c l 0 r'
        if v1 >= 1 and v2 == 0:  # | .c l (j + 1) 0
            l = v0
            j = v1 - 1
            return ('d', (l), (j), (1)), 'c l j+1 0'
        if v1 >= 1 and v2 >= 1:  # | .c l (j + 1) (r + 1)
            l = v0
            j = v1 - 1
            r = v2 - 1
            return ('d', (l), (j + 1), (r + 1)), 'c l j+1 r+1'
    if tag == 'd':
        v0, v1, v2 = s[1:]
        if v1 == 0 and v2 == 0:  # | .d l 0 0
            l = v0
            return ('e', (l + 1), (1)), 'd l 0 0'
        if v1 == 0 and v2 == 1:  # | .d l 0 1
            l = v0
            return None, 'd l 0 1'
        if v1 == 0 and v2 == 2:  # | .d l 0 2
            l = v0
            return ('f', (l + 1), (0)), 'd l 0 2'
        if v1 == 0 and v2 >= 3:  # | .d l 0 (r + 3)
            l = v0
            r = v2 - 3
            return ('a', (l + 1), (0), (r + 1)), 'd l 0 r+3'
        if v1 == 1 and v2 == 0:  # | .d l 1 0
            l = v0
            return None, 'd l 1 0'
        if v1 == 1 and v2 == 1:  # | .d l 1 1
            l = v0
            return ('c', (l + 4), (0), (0)), 'd l 1 1'
        if v1 == 1 and v2 == 2:  # | .d l 1 2
            l = v0
            return ('b', (l + 2), (0), (1)), 'd l 1 2'
        if v1 == 1 and v2 >= 3:  # | .d l 1 (r + 3)
            l = v0
            r = v2 - 3
            return ('b', (l + 2), (1), (r + 1)), 'd l 1 r+3'
        if v1 == 2:  # | .d l 2 r
            l = v0
            r = v2
            return ('c', (l + 4), (0), (r)), 'd l 2 r'
        if v1 >= 3 and v2 == 0:  # | .d l (j + 3) 0
            l = v0
            j = v1 - 3
            return ('c', (l + 4), (j), (1)), 'd l j+3 0'
        if v1 >= 3 and v2 >= 1:  # | .d l (j + 3) (r + 1)
            l = v0
            j = v1 - 3
            r = v2 - 1
            return ('c', (l + 4), (j + 1), (r + 1)), 'd l j+3 r+1'
    if tag == 'e':
        v0, v1 = s[1:]
        if v0 == 0 and v1 == 0:  # | .e 0 0
            return ('d', (0), (0), (1)), 'e 0 0'
        if v0 == 0 and v1 >= 1:  # | .e 0 (j + 1)
            j = v1 - 1
            return ('d', (0), (0), (2 * j + 3)), 'e 0 j+1'
        if v0 == 1 and v1 == 0:  # | .e 1 0
            return ('d', (0), (1), (1)), 'e 1 0'
        if v0 == 1 and v1 >= 1:  # | .e 1 (j + 1)
            j = v1 - 1
            return ('d', (0), (1), (2 * j + 3)), 'e 1 j+1'
        if v0 >= 2 and v1 == 0:  # | .e (l + 2) 0
            l = v0 - 2
            return ('b', (l), (0), (1)), 'e l+2 0'
        if v0 >= 2 and v1 >= 1:  # | .e (l + 2) (j + 1)
            l = v0 - 2
            j = v1 - 1
            return ('b', (l), (0), (2 * j + 3)), 'e l+2 j+1'
    if tag == 'f':
        v0, v1 = s[1:]
        if v1 == 0:  # | .f l 0
            l = v0
            return ('b', (l), (1), (1)), 'f l 0'
        if v1 >= 1:  # | .f l (j + 1)
            l = v0
            j = v1 - 1
            return ('e', (l), (j + 4)), 'f l j+1'
    raise Stuck('no case of next matches %r' % (s,))


# The same cases as data for accel (generated from the same parse of `next`; accel is checked against step).
# tag -> [(conds per component: ('=', c) | ('>=', c), None | (tag2, affine forms (const, ((i, coef), ...))))]
RULES = {'a': [((('>=', 0), ('>=', 0), ('=', 0)), ('f', ((0, ((0, 1),)), (0, ((1, 1),))))),
       ((('=', 0), ('>=', 0), ('>=', 1)), ('d', ((0, ()), (1, ((1, 1),)), (2, ((2, 1),))))),
       ((('>=', 1), ('>=', 0), ('>=', 1)), ('b', ((-1, ((0, 1),)), (0, ((1, 1),)), (2, ((2, 1),)))))],
 'b': [((('>=', 0), ('>=', 0), ('=', 0)), ('e', ((0, ((0, 1),)), (1, ((1, 1),))))),
       ((('>=', 0), ('>=', 0), ('=', 1)), ('e', ((0, ((0, 1),)), (2, ((1, 1),))))),
       ((('>=', 0), ('>=', 0), ('=', 2)), None),
       ((('>=', 0), ('>=', 0), ('=', 3)), ('f', ((0, ((0, 1),)), (1, ((1, 1),))))),
       ((('>=', 0), ('>=', 0), ('>=', 4)), ('a', ((0, ((0, 1),)), (1, ((1, 1),)), (-3, ((2, 1),)))))],
 'c': [((('>=', 0), ('=', 0), ('>=', 0)), ('d', ((0, ((0, 1),)), (0, ()), (0, ((2, 1),))))),
       ((('>=', 0), ('>=', 1), ('=', 0)), ('d', ((0, ((0, 1),)), (-1, ((1, 1),)), (1, ())))),
       ((('>=', 0), ('>=', 1), ('>=', 1)), ('d', ((0, ((0, 1),)), (0, ((1, 1),)), (0, ((2, 1),)))))],
 'd': [((('>=', 0), ('=', 0), ('=', 0)), ('e', ((1, ((0, 1),)), (1, ())))), ((('>=', 0), ('=', 0), ('=', 1)), None),
       ((('>=', 0), ('=', 0), ('=', 2)), ('f', ((1, ((0, 1),)), (0, ())))),
       ((('>=', 0), ('=', 0), ('>=', 3)), ('a', ((1, ((0, 1),)), (0, ()), (-2, ((2, 1),))))),
       ((('>=', 0), ('=', 1), ('=', 0)), None),
       ((('>=', 0), ('=', 1), ('=', 1)), ('c', ((4, ((0, 1),)), (0, ()), (0, ())))),
       ((('>=', 0), ('=', 1), ('=', 2)), ('b', ((2, ((0, 1),)), (0, ()), (1, ())))),
       ((('>=', 0), ('=', 1), ('>=', 3)), ('b', ((2, ((0, 1),)), (1, ()), (-2, ((2, 1),))))),
       ((('>=', 0), ('=', 2), ('>=', 0)), ('c', ((4, ((0, 1),)), (0, ()), (0, ((2, 1),))))),
       ((('>=', 0), ('>=', 3), ('=', 0)), ('c', ((4, ((0, 1),)), (-3, ((1, 1),)), (1, ())))),
       ((('>=', 0), ('>=', 3), ('>=', 1)), ('c', ((4, ((0, 1),)), (-2, ((1, 1),)), (0, ((2, 1),)))))],
 'e': [((('=', 0), ('=', 0)), ('d', ((0, ()), (0, ()), (1, ())))),
       ((('=', 0), ('>=', 1)), ('d', ((0, ()), (0, ()), (1, ((1, 2),))))),
       ((('=', 1), ('=', 0)), ('d', ((0, ()), (1, ()), (1, ())))),
       ((('=', 1), ('>=', 1)), ('d', ((0, ()), (1, ()), (1, ((1, 2),))))),
       ((('>=', 2), ('=', 0)), ('b', ((-2, ((0, 1),)), (0, ()), (1, ())))),
       ((('>=', 2), ('>=', 1)), ('b', ((-2, ((0, 1),)), (0, ()), (1, ((1, 2),)))))],
 'f': [((('>=', 0), ('=', 0)), ('b', ((0, ((0, 1),)), (1, ()), (1, ())))),
       ((('>=', 0), ('>=', 1)), ('e', ((0, ((0, 1),)), (3, ((1, 1),)))))]}


def accel(s):
    """Batch a run of identical translation cycles exactly (maps/_cycle.py); else one plain step."""
    r = cycle_accel(RULES, s)
    if r is not None:
        return r
    s2, lab = step(s)
    return s2, 1, lab
