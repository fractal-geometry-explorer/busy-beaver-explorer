"""1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB is the mirror image of 1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD
started in another state.

1. Tables (exact): reflect this machine (swap L and R) and rename its states A,B,C,D,E,F to C,D,E,A,B,F: the result
   is the table of the other machine, entry by entry. So this machine from blank tape is the mirror image of the other
   one started on blank tape in its state C.
2. The other machine from blank tape (state A) is after three steps in state C on a blank cell with a single 1 on
   its right. That is the same configuration with one 1 more, and that 1 is the first cell of the run of 1s (the visit
   counter). The irregular
   word W never sees how long the run is, so the two runs stay in step: at every visit of the far end the word W is
   the same, cell for cell (mirrored), and this machine's run is one cell shorter. Checked here at every visit
   (default 1,200 visits); `c/runsim.c` gives the same at 3*10^7 visits.

usage: python3 sibling.py [visits]
"""
import sys

THIS = "1RB1RA_1LC1RE_---0LD_1LE1LD_0RA0LF_1LF0LB"
OTHER = "1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD"
PERM = {0: 2, 1: 3, 2: 4, 3: 0, 4: 1, 5: 5}          # this machine's state -> the other machine's state


def parse(m):
    t = {}
    for i, r in enumerate(m.split("_")):
        for b in (0, 1):
            x = r[3 * b:3 * b + 3]
            t[(i, b)] = None if x[0] == "-" else (int(x[0]), 1 if x[1] == "R" else -1, ord(x[2]) - 65)
    return t


def visits(t, climb, nv, mirror):
    """(W, run length) each time the climbing state stands on the blank beyond the run."""
    tape, p, s, d = {}, 0, 0, (-1 if mirror else 1)
    out = []
    while len(out) < nv:
        if s == climb and tape.get(p, 0) == 0 and all(k * d < p * d for k, v in tape.items() if v):
            ks = [k * d for k, v in tape.items() if v]
            x = "".join(str(tape.get(i * d, 0)) for i in range(min(ks), p * d)) if ks else ""
            w = x.rstrip("1")
            out.append((w, len(x) - len(w)))
        w_, dd, ns = t[(s, tape.get(p, 0))]
        tape[p] = w_
        p += dd
        s = ns
    return out


def main():
    nv = int(sys.argv[1]) if len(sys.argv) > 1 else 1200
    a, b = parse(THIS), parse(OTHER)
    for (s, x), u in a.items():
        v = b[(PERM[s], x)]
        assert (u is None and v is None) or (u[0] == v[0] and u[1] == -v[1] and PERM[u[2]] == v[2]), (s, x)
    print("tables: this machine = mirror image of the other with states A,B,C,D,E,F -> C,D,E,A,B,F")
    va = visits(a, 3, nv, True)            # this machine climbs in D (the other's A), towards the left
    vb = visits(b, 0, nv + 1, False)
    # the other machine's first visit is `A>` on the empty tape; from its second on they correspond
    for i in range(nv):
        assert va[i][0] == vb[i + 1][0] and va[i][1] + 1 == vb[i + 1][1], i
    print("in step at %d visits: same word W (mirrored), run one cell shorter (last: run %d and %d, W %d cells)"
          % (nv, va[-1][1], vb[-1][1], len(va[-1][0])))


if __name__ == "__main__":
    main()
