"""The 40 machines of the block-list family, and how each one is the same five-state core seen in a frame.

Frame A is the core as 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_?--- writes it: states A..E do all the work, F is entered
only by the rare transition D1 -> 0LF or 1LF ("an F-event"), and F1 is the halting transition.  The machines differ
in the bit D1 writes, in F0 and in the start state (A, C, E or F in frame A).  Every machine of the
family is, transition for transition, either a frame-A machine or the mirror image (L <-> R) of one under a
renaming of the states; `conjugate` checks that on the tables, so the runs from blank tape correspond exactly
(the mirror image of the tape, the renamed state, the same step count), with the start state given here.
"""
STATES = "ABCDEF"

# frame-B machines (1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_?): mirror image of frame A, frame-A state -> this state
TO_B = {"A": "D", "B": "E", "C": "A", "D": "B", "E": "C", "F": "F"}
# the X machine 1RB---_0LC0LB_1RF0LD_1RE0RB_1LB0RC_0RD1RA: mirror image, frame-A state -> this state
TO_X = {"A": "E", "B": "B", "C": "C", "D": "F", "E": "D", "F": "A"}

# frame-G machines (1RB0RC_1LC0RD_0LD0LC_1RE0LA_?_?): mirror image, frame-A state -> this state
TO_G = {"A": "B", "B": "C", "C": "D", "D": "E", "E": "A", "F": "F"}

FAMILY = [
    # machine, frame, frame-A machine it is conjugate to, frame-A start state
    # the 14 machines of the first pass (group G01)
    ("1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---", "A", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---", "A"),
    ("1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RB---", "A", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RB---", "A"),
    ("1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE---", "A", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE---", "A"),
    ("1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---", "A", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---", "A"),
    ("1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LC---", "A", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LC---", "A"),
    ("1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---", "A", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---", "A"),
    ("1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LD---", "B", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---", "C"),
    ("1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0LE---", "B", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RB---", "C"),
    ("1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RA---", "B", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LC---", "C"),
    ("1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1LD---", "B", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---", "C"),
    ("1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RA---", "B", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LC---", "C"),
    ("1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RE---", "B", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---", "C"),
    ("1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LD---", "B", "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1RA---", "C"),
    ("1RB---_0LC0LB_1RF0LD_1RE0RB_1LB0RC_0RD1RA", "X", "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LB---", "F"),
    # the other 26 machines with the same core (first analysed as groups G02, G04, G05 and G06)
    ("1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LC---", "A", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LC---", "A"),
    ("1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LE---", "A", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LE---", "A"),
    ("1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LA---", "A", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LA---", "A"),
    ("1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LB---", "A", "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LB---", "A"),
    ("1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LD---", "A", "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LD---", "A"),
    ("1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RE---", "A", "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RE---", "A"),
    ("1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LB---", "A", "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LB---", "A"),
    ("1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LD---", "A", "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LD---", "A"),
    ("1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RC---", "B", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LE---", "C"),
    ("1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0LA---", "B", "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RC---", "C"),
    ("1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0RB---", "B", "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LD---", "C"),
    ("1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0RE---", "B", "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LB---", "C"),
    ("1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RB---", "B", "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LD---", "C"),
    ("1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RE---", "B", "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LB---", "C"),
    ("1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LA---", "G", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE---", "E"),
    ("1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LB---", "G", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---", "E"),
    ("1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0LC---", "G", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RB---", "E"),
    ("1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RA---", "G", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LE---", "E"),
    ("1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RD---", "G", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LC---", "E"),
    ("1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1LB---", "G", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RA---", "E"),
    ("1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1RC---", "G", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LB---", "E"),
    ("1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1RD---", "G", "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LC---", "E"),
    ("1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0LD---", "G", "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RC---", "E"),
    ("1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RC---", "G", "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LB---", "E"),
    ("1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RE---", "G", "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LD---", "E"),
    ("1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_1RE---", "G", "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LD---", "E"),
]

# the 14 machines of the first pass, whose records write_records.py writes
FIRST = FAMILY[:14]


def parse(m):
    t = {}
    for i, g in enumerate(m.split("_")):
        for y in (0, 1):
            s = g[3 * y:3 * y + 3]
            t[(STATES[i], y)] = None if s[2] == "-" else (int(s[0]), s[1], s[2])
    return t


def conjugate(machine, frame_a, mapping, mirror=True):
    """True if `machine` is the image of `frame_a` under the state map (frame-A state -> machine state) and,
    when `mirror`, the exchange of L and R."""
    a, b = parse(frame_a), parse(machine)
    flip = {"L": "R", "R": "L"} if mirror else {"L": "L", "R": "R"}
    for s in STATES:
        for y in (0, 1):
            x, z = a[(s, y)], b[(mapping[s], y)]
            if (x is None) != (z is None):
                return False
            if x is not None and (x[0] != z[0] or flip[x[1]] != z[1] or mapping[x[2]] != z[2]):
                return False
    return True


def frame_map(frame):
    return {"A": {s: s for s in STATES}, "B": TO_B, "X": TO_X, "G": TO_G}[frame]


def info(machine):
    for m, fr, fa, st in FAMILY:
        if m == machine:
            return fr, fa, st
    raise KeyError(machine)


def core_frames(machine):
    """every way to see `machine` as the frame-A core: (frame-A machine, frame-A start state, mirrored) for each
    renaming of the states (all 720) and each orientation under which states A, B, C, E and D0 of the image are
    those of the core and F1 is the halting transition.  Empty for a machine outside the family."""
    import itertools
    core = parse("1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_------")
    t = parse(machine)
    out = []
    for p in itertools.permutations(STATES):
        perm = dict(zip(STATES, p))            # this machine's state -> frame-A state
        for mirror in (False, True):
            flip = {"L": "R", "R": "L"} if mirror else {"L": "L", "R": "R"}
            o = {(perm[s], y): None if v is None else (v[0], flip[v[1]], perm[v[2]]) for (s, y), v in t.items()}
            if any(o[k] != core[k] for k in core if k[0] in "ABCE" or k == ("D", 0)):
                continue
            d = o[("D", 1)]
            if d is None or d[1:] != ("L", "F") or o[("F", 1)] is not None or o[("F", 0)] is None:
                continue
            fa = "_".join("".join("---" if o[(s, y)] is None else "%d%s%s" % o[(s, y)] for y in (0, 1))
                          for s in STATES)
            out.append((fa, perm["A"], mirror))
    return out


def check_all():
    out = []
    for m, fr, fa, st in FAMILY:
        mp = frame_map(fr)
        ok = conjugate(m, fa, mp, mirror=(fr != "A"))
        # the start: the machine starts in A, which must be the image of the frame-A start state
        ok = ok and mp[st] == "A"
        # and the brute-force search over all renamings finds exactly this frame
        ok = ok and core_frames(m) == [(fa, st, fr != "A")]
        out.append((m, fr, fa, st, ok))
    return out


if __name__ == "__main__":
    for row in check_all():
        print(*row)


def _toks(s):
    return s.split()


def _rev_tok(t):
    """mirror one token of a configuration string: words reversed, contexts swapped"""
    if t == "0^inf":
        return t
    if t.startswith("("):
        w, e = t[1:].split(")^")
        return f"({w[::-1]})^{e}"
    if t in ("L", "R"):
        return {"L": "R", "R": "L"}[t]
    if t.isdigit():
        return t[::-1]
    return t


def translate(cfg, frame):
    """a frame-A configuration string 'L ... S> x ...' as the configuration of a machine of `frame`"""
    if frame == "A":
        return cfg
    mp = frame_map(frame)
    parts = cfg.split()
    i = next(k for k, p in enumerate(parts) if p.endswith(">") and len(p) == 2)
    left, st, right = parts[:i], parts[i][0], parts[i + 1:]
    head, rest = right[0], right[1:]
    assert head in ("0", "1"), "the head cell must be a literal"
    new_left = [_rev_tok(t) for t in reversed(rest)]
    new_right = [head] + [_rev_tok(t) for t in reversed(left)]
    return " ".join(new_left + [mp[st] + ">"] + new_right)
