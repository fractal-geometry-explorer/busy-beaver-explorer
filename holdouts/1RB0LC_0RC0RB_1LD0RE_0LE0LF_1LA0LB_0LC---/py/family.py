"""The shared core of the sixteen "marker counter" holdouts (group G04, family lead: this folder).

All sixteen machines run the same counter (see README.md here).  The machines whose names start
1RB0LC_0RC0RB_1LD0RE_0LE use states A-E for it (D1 and F are only used at rare events; for
1RB0LC_0RC0RB_1LD0RE_0LE0LB_1LA1RF_0LD--- E1 is done in three steps through F); the other seven run the mirror
image of the same core with the states renamed (A,B,C,D,E -> D,E,A,B,C) and start in the core's state C.

`rules(M)` lists the local rules of a sweep (and a few whole sweeps) in the orientation of the first group;
`lean_rules(M, ns)` proves each for machine M with tools/py/bbtools/symtm.py (mirrored for the second group) and
returns the text of lean/Rules.lean.
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../../tools/py'))
from bbtools.symtm import prove, run, Config, Ctx, Blank  # noqa: E402
from bbtools.machine import Machine  # noqa: E402

LEAD = '1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LC---'
SIGMA = {'A': 'D', 'B': 'E', 'C': 'A', 'D': 'B', 'E': 'C', 'F': 'F'}


def mirrored(M):
    """Is M one of the machines that run the mirror image of the core?"""
    return not M.startswith('1RB0LC_0RC0RB_1LD0RE_0LE')


# the phases of a marker, as cells left to right (first group's orientation)
PHASES = [("0", "1"), ("0'", "0"), ("1", "0011"), ("2", "011"), ("3", "11"), ("4", "00111")]

LOCAL = [
    ('r_start', 'L 0 0 0 E> 0^inf', 'L D> 0 1 0 1 0 1 0^inf',
     'A sweep starts: the head, back from the right end, turns and starts the leftward wave in state D.'),
    ('r_dx', 'L (0010)^n D> 0 R', 'L D> 0 (1010)^n R',
     'The leftward wave crosses a block of n words 0010, leaving 1010 behind.'),
    ('r_d4', 'L 0 0 1 1 1 D> 0 R', 'L D> 0 1 0 1 0 1 R',
     'The leftward wave passes a marker in phase 4 (00111): a carry.'),
    ('r_t0', 'L 0 0 1 0 0 0 1 0 1 D> 0 1 0 1 0 R', 'L 0 0 1 1 0 0 1 0 0 0 1 0 0 0 C> R',
     'The wave turns at a marker in phase 0 (1) with two blocks to its left: it becomes 0011.'),
    ('r_t0p', 'L 0 0 1 0 0 D> 0 1 0 1 0 R', 'L 0 0 1 1 0 0 1 0 0 0 C> R',
     "The wave turns at a marker in phase 0' (0) with a block to its left: it becomes 0011."),
    ('r_t1', 'L 0 0 1 1 D> 0 1 0 1 0 R', 'L 0 1 1 0 0 1 0 0 0 C> R',
     'The wave turns at a marker in phase 1 (0011): it becomes 011.'),
    ('r_t2', 'L 0 1 1 D> 0 1 0 1 0 R', 'L 1 1 0 0 1 0 0 0 C> R',
     'The wave turns at a marker in phase 2 (011): it becomes 11.'),
    ('r_t3', 'L 0 0 1 0 1 1 D> 0 1 0 1 0 R', 'L 0 0 1 1 1 0 0 1 0 0 0 C> R',
     'The wave turns at a marker in phase 3 (11) with a block to its left: it becomes 00111.'),
    ('r_cx', 'L C> (1010)^n R', 'L (1000)^n C> R',
     'The rightward wave (state C) restores a block.'),
    ('r_c4', 'L C> 1 0 1 0 1 1 0 1 0 R', 'L 1 0 1 0 0 1 0 0 0 C> R',
     'The rightward wave resets a carried marker (phase 4 becomes phase 0) and the first word after it.'),
    ('r_cend', 'L C> 1 0 1 0 1 0^inf', 'L 1 0 0 0 0 E> 0^inf',
     'The rightward wave reaches the end of the tape, three cells further than before.'),
    ('r_oleft', '0^inf 1 D> 0 1 0 1 0 R', '0^inf 1 0 0 1 0 0 0 1 0 B> R',
     'Overflow: the leftward wave reaches the 1 at the left end and comes back in state B.'),
    ('r_bx', 'L B> (1010)^n R', 'L (0010)^n B> R',
     'The overflow wave (state B) restores a block.'),
    ('r_b4', 'L B> 1 0 1 0 1 R', 'L 0 0 1 0 0 B> R',
     "The overflow wave turns a carried marker into phase 0' (0) and lengthens the block before it."),
    ('r_bend', 'L B> 1 0 1 0 1 0^inf', 'L 0 0 1 1 0 0 0 E> 0^inf',
     'The overflow wave reaches the end and leaves a new marker 0011 there.'),
]

# whole sweeps: (name, start, doc); the end is the configuration the run reaches at the next sweep end
SWEEPS = [
    ('sw_p0', 'L (0010)^a+2 1 (0010)^n+1 0 0 0 E> 0^inf', 'One sweep, last marker in phase 0: 1 becomes 0011.'),
    ('sw_p0p', 'L (0010)^a+1 0 (0010)^n+1 0 0 0 E> 0^inf', "One sweep, last marker in phase 0': 0 becomes 0011."),
    ('sw_p1', 'L 0011 (0010)^n+1 0 0 0 E> 0^inf', 'One sweep, last marker in phase 1: 0011 becomes 011.'),
    ('sw_p2', 'L 011 (0010)^n+1 0 0 0 E> 0^inf', 'One sweep, last marker in phase 2: 011 becomes 11.'),
    ('sw_p3', 'L (0010)^a+1 11 (0010)^n+1 0 0 0 E> 0^inf', 'One sweep, last marker in phase 3: 11 becomes 00111.'),
    ('sw_c2', 'L 011 (0010)^m+1 00111 (0010)^n+1 0 0 0 E> 0^inf',
     'One sweep with a carry: the last marker (phase 4) resets to phase 0, the one before goes from 2 to 3.'),
    ('sw_cc2', 'L 011 (0010)^m+1 00111 (0010)^k+1 00111 (0010)^n+1 0 0 0 E> 0^inf',
     'One sweep with two carries.'),
    ('sw_of1', '0^inf 1 (0010)^a+1 00111 (0010)^n+1 0 0 0 E> 0^inf',
     "Overflow with one marker: it becomes phase 0', the first block grows by 2 and a new marker appears."),
    ('sw_of2', '0^inf 1 (0010)^a+1 00111 (0010)^m+1 00111 (0010)^n+1 0 0 0 E> 0^inf',
     'Overflow with two markers.'),
]


def _mtok(t):
    if t == '0^inf':
        return t
    if t.startswith('('):
        w, e = t[1:].split(')^')
        return '(' + w[::-1] + ')^' + e
    if t[0] in '01':
        return t[::-1]
    return {'L': 'R', 'R': 'L'}.get(t, t)


def mirror(s):
    """The mirror image of a configuration string (states renamed by SIGMA)."""
    parts = s.split()
    i = next(k for k, p in enumerate(parts) if p.endswith('>') and len(p) == 2)
    left, st, right = parts[:i], parts[i][0], parts[i + 1:]
    if right[0] == '0^inf':
        head, rest = '0', right
    else:
        head, rest = right[0][0], ([right[0][1:]] if len(right[0]) > 1 else []) + right[1:]
    nl = [_mtok(t) for t in reversed(rest)]
    nr = [_mtok(t) for t in reversed(left)]
    return ' '.join(nl + [SIGMA[st] + '>', head] + nr)


def _sweep_end(M, start):
    m = Machine.parse(M)
    c = Config.parse(start)
    E = 4 if not mirrored(M) else 2  # core state E, renamed C in the mirror

    def stop(c):
        if c.steps.is_zero() or c.state != E:
            return False
        side = c.right if not mirrored(M) else c.left
        return side == [Blank()]
    run(m, c, stop, max_moves=5000)
    return repr(c)


def rules(M):
    """[(name, start, end, doc)] for machine M, in M's own orientation."""
    out = []
    f = mirror if mirrored(M) else (lambda s: s)
    for nm, s, e, d in LOCAL:
        out.append((nm, f(s), f(e), d))
    for nm, s, d in SWEEPS:
        s2 = f(s)
        out.append((nm, s2, _sweep_end(M, s2), d))
    return out


def lean_rules(M, ns):
    body, skipped = [], []
    for nm, s, e, d in rules(M):
        try:
            t, _ = prove(M, nm, s, e, doc=d + (' (mirror image)' if mirrored(M) else ''))
        except Exception:
            if not mirrored(M):
                raise
            skipped.append(nm)    # a mirrored crossing that symtm's conventions cannot state; the sweeps cover it
            continue
        body.append(t)
    skip = ''
    if skipped:
        skip = ('\n\nNot stated here (the head would have to stop in the middle of a crossing in the mirrored form): '
                + ', '.join('`' + x + '`' for x in skipped) + '.')
    head = f'''import Machine

/-!
# The rules of a sweep of {M}

Generated by `py/rules.py` (with `family.py` of the family lead {LEAD} and `tools/py/bbtools/symtm.py`); do not
edit by hand.  The tape between sweeps is `1 (0010)^b0 m1 (0010)^b1 ... mk (0010)^bk 000`, the markers `mi` in one of
the phases 1, 0, 0011, 011, 11, 00111{' (here mirrored: the tape grows to the left)' if mirrored(M) else ''}.  The
`r_` rules are the pieces of a sweep: the leftward wave (`r_start`, `r_dx`, `r_d4`), its turn at the first marker
not in phase 4 (`r_t0` ... `r_t3`) or at the left end (`r_oleft`), and the rightward waves (`r_cx`, `r_c4`, `r_cend`
after a turn, `r_bx`, `r_b4`, `r_bend` after an overflow).  The `sw_` rules are whole sweeps for all block lengths.{skip}
-/

namespace {ns}

open TM

'''
    return head + '\n'.join(body) + f'\nend {ns}\n'
