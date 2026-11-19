"""The seven vampire-family holdouts as one machine core with three F0 variants.

Every machine of the family is, after renaming the states (and, for one of them, mirroring the tape), the core

    A 1RB0LA   B 0RC0RB   C 1LD1LA   D 1LC1RE   E 1RF0RD   F ??? ---

with F0 (state F reading 0) one of 1LC, 1LA, 1RB, started in A, E or F.  This module finds that renaming for each
machine, simulates the core, measures the E-event map, and is imported by gen.py (the Lean generator).

An E-event is `c E> 1^n` (blank beyond), entered by D1 -> 1RE not right after E1 -> 0RD; c is the tape from its
first 1 to the head (the context).  For every variant the E-pass turns it into `Cn c m` (b = 0, m even) or
`Cn (c 1) m` (b = 1, m odd), the head in C on the first cell of a block of m ones, with
m = 2u + 2 + 3q and b = q mod 2, where q = n/2 - 1 + e (n even) or (n - 3)/2 + f (n odd) and the block left by
the E-pass is 2u + 2 (n even) or 2v + 2 (n odd) long:

    F0     e  u   f  v
    1LC    1  0   0  3
    1LA    0  1   1  1
    1RB    0  2   1  2

What the context then does with the block depends only on the context and b (the rewrite, `rule`).

usage: python3 family.py match            the renaming of each machine onto the core
       python3 family.py first            the first E-events of each machine's run from blank tape
       python3 family.py rule F0 CTX      the two rewrites of a context
"""
import itertools
import sys

CORE = "1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_"
VARIANTS = {"1LC": (1, 0, 0, 3), "1LA": (0, 1, 1, 1), "1RB": (0, 2, 1, 2)}
NS = {"1LC": "VLC", "1LA": "VLA", "1RB": "VRB"}

# (TNF name, bbchallenge id, label in the vampire-family repository)
FAMILY = [
    ("1RB---_1LC0RB_0LD0LC_1RE1RB_1RD1LF_1LA0LE", 21328, "TM1"),
    ("1RB0RF_1LC---_1RD0LC_0RE0RD_1LF1LC_1LE1RA", 119593, "TM1-F"),
    ("1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---", 121010, "TM2"),
    ("1RB0RE_1RC---_0RD0RC_1LE1LF_1LD1RA_1RC0LF", 92948, "TM2'"),
    ("1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LA---", 160156, "TM2a"),
    ("1RB---_0RC0RB_1LD1LE_1LC1RF_1RB0LE_1RA0RD", 82614, "TM2b"),
    ("1RB0RF_1LC---_1LF1LD_1RE0LD_0RC0RE_1LC1RA", 134470, "TM2b'"),
]


def parse(m):
    t = {}
    for s, part in enumerate(m.split("_")):
        for b in (0, 1):
            x = part[3 * b:3 * b + 3]
            t[(s, b)] = None if x[2] == "-" else (int(x[0]), x[1], ord(x[2]) - 65)
    return t


def match(m):
    """[(perm, mirrored, F0, start)]: perm[core state] = machine state; start = the core state of machine state A"""
    t, c, res = parse(m), parse(CORE + "1LC---"), []
    flip = {"L": "R", "R": "L"}
    for perm in itertools.permutations(range(6)):
        for mir in (False, True):
            ok = True
            for (s, b), v in c.items():
                if s == 5:
                    continue
                w = t[(perm[s], b)]
                if w is None or (w[0], flip[w[1]] if mir else w[1], w[2]) != (v[0], v[1], perm[v[2]]):
                    ok = False
                    break
            if ok and t[(perm[5], 1)] is None and t[(perm[5], 0)] is not None:
                inv = {perm[i]: i for i in range(6)}
                f0 = t[(perm[5], 0)]
                d = flip[f0[1]] if mir else f0[1]
                res.append((perm, mir, f"{f0[0]}{d}{'ABCDEF'[inv[f0[2]]]}", "ABCDEF"[inv[0]]))
    return res


def core(f0):
    return CORE + f0 + "---"


def simulate(f0, tape, h, st, maxsteps, on_event=None):
    """run the core variant; on_event(s, c, n) is called at every E-event (return True to stop).
    Returns ('HALT', s) / ('STOP', s) / ('MAX', s)."""
    t = parse(core(f0))
    p1 = p2 = None
    for s in range(1, maxsteps + 1):
        b = tape.get(h, 0)
        tr = t[(st, b)]
        if tr is None:
            return ("HALT", s - 1)
        tape[h] = tr[0]
        h += 1 if tr[1] == "R" else -1
        p2, p1 = p1, (st, b)
        st = tr[2]
        if on_event and st == 4 and p1 == (3, 1) and p2 != (4, 1) and tape.get(h, 0) == 1:
            ones = [k for k, v in tape.items() if v]
            hi, lo = max(ones), min(ones)
            if lo < h and all(tape.get(i, 0) == 1 for i in range(h, hi + 1)):
                c = "".join(str(tape.get(i, 0)) for i in range(lo, h))
                if on_event(s, c, hi - h + 1):
                    return ("STOP", s)
    return ("MAX", maxsteps)


def first_event(f0, start, nmin=6):
    """(steps, context, n) of the first E-event with n >= nmin from blank tape in core state `start`"""
    out = []

    def ev(s, c, n):
        if n >= nmin:
            out.append((s, c, n))
            return True
        return False
    r = simulate(f0, {}, 0, "ABCDEF".index(start), 10 ** 6, ev)
    assert r[0] == "STOP", r
    return out[0]


def rewrite(f0, c, b, j):
    """from `c C> 1^(2j+2)` (b = 0) or `c 1 C> 1^(2j+5)` (b = 1): ('HALT', steps) or (c', n', steps)"""
    left = c + ("1" if b else "")
    m = 2 * j + 2 if b == 0 else 2 * j + 5
    tape = {i - len(left): int(ch) for i, ch in enumerate(left)}
    for i in range(m):
        tape[i] = 1
    out = []

    def ev(s, c2, n):
        out.append((c2, n, s))
        return True
    r = simulate(f0, tape, 0, 2, 10 ** 7, ev)
    if r[0] == "HALT":
        return ("HALT", r[1])
    assert r[0] == "STOP", (f0, c, b, r)
    return out[0]


_rules = {}


def rule(f0, c, b):
    """(c', a): the rewrite takes the block m to the E-event n' = m + a; or 'HALT'"""
    k = (f0, c, b)
    if k not in _rules:
        j1, j2 = 40 + 10 * len(c), 81 + 10 * len(c)
        r1, r2 = rewrite(f0, c, b, j1), rewrite(f0, c, b, j2)
        if r1[0] == "HALT":
            assert r2[0] == "HALT", (k, r1, r2)
            _rules[k] = "HALT"
        else:
            m1 = 2 * j1 + 2 + 3 * b
            m2 = 2 * j2 + 2 + 3 * b
            assert r1[0] == r2[0] and r1[1] - m1 == r2[1] - m2, (k, r1, r2)
            _rules[k] = (r1[0], r1[1] - m1)
    return _rules[k]


def next_event(f0, c, n):
    """the map, from the variant's constants and `rule`: (c', n') or 'HALT'"""
    e, u, f, v = VARIANTS[f0]
    if n % 2 == 0:
        q, m = n // 2 - 1 + e, None
        m = 2 * u + 2 + 3 * q
    else:
        q = (n - 3) // 2 + f
        m = 2 * v + 2 + 3 * q
    r = rule(f0, c, q % 2)
    return r if r == "HALT" else (r[0], m + r[1])


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "match":
        for m, i, lab in FAMILY:
            print(m, lab, match(m))
    elif cmd == "first":
        for m, i, lab in FAMILY:
            perm, mir, f0, st = match(m)[0]
            print(m, lab, f0, st, first_event(f0, st))
    elif cmd == "rule":
        for b in (0, 1):
            print(sys.argv[3], "b =", b, rule(sys.argv[2], sys.argv[3], b))
    elif cmd == "check":
        # the map against direct simulation of the run from blank tape (events with n >= 6)
        for m, i, lab in FAMILY:
            perm, mir, f0, st = match(m)[0]
            evs = []

            def ev(s, c, n):
                if n >= 6:
                    evs.append((c, n))
                return len(evs) >= 14
            simulate(f0, {}, 0, "ABCDEF".index(st), 10 ** 9, ev)
            ok = all(next_event(f0, *evs[i]) == evs[i + 1] for i in range(len(evs) - 1))
            print(lab, f0, st, len(evs), "events, map agrees" if ok else "MISMATCH")
