"""The phases of 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---: a Collatz-like map M -> 8M/3 + c with a small stack.

usage: python3 phases.py [PHASES]        (default 3000; a minute)

A phase starts at PS(M, T): the head in state F on the blank cell left of `1^M`, followed by the tail T, a list of
blocks `0 1^t`, then blank tape.  The phase ends at the next PS(M', T').  Within a phase the machine runs the rounds
proved in lean/Rules.lean (`start`, `round`); this script does not use them, it runs the machine.

`nextps(M, T)` runs the machine from PS(M, T) to the next PS.  `phase(M, T)` gets PS(M', T') for any M, however
large: it runs `nextps` on three small M0 = base, base + 3, base + 6 with the same residue M mod 3 and the same
tail, checks that the three results have the same tail and M' = 8 M0 / 3 + c, and extrapolates.  (That M' is linear
in M within a residue class is checked here at three points per class, not proved.)

1. checks `phase` against the plain machine for the first ten phases from blank tape (to step 1.2e9 they are
   PS(9, []) PS(27, []) ... PS(73761, []), found by the plain run of the C simulator; listed in BLANK below);
2. lists which small tails make the machine halt (every tail of up to 3 blocks of 1..8 ones, each residue);
3. iterates `phase` from PS(9, []) for PHASES phases, printing the largest tail seen and any halt.
"""
import itertools
import sys
from fractions import Fraction

M = "1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---"


def table(m):
    t = {}
    for s, grp in enumerate(m.split("_")):
        for r in range(2):
            w = grp[3 * r:3 * r + 3]
            t[(s, r)] = None if w[0] == "-" else (int(w[0]), 1 if w[1] == "R" else -1, ord(w[2]) - 65)
    return t


T = table(M)
# the phase starts of the run from blank tape (step, M, tail), from `recrle` / the plain simulator
BLANK = [(36, 9, ()), (226, 27, ()), (1430, 75, ()), (9562, 203, ()), (66753, 545, ()), (468794, 1457, ()),
         (3315299, 3889, ()), (23503104, 10365, (6,)), (166999736, 27659, ()), (1187331039, 73761, ())]


def rle(cells):
    out, i = [], 0
    while i < len(cells):
        j = i
        while j < len(cells) and cells[j] == cells[i]:
            j += 1
        out.append((cells[i], j - i))
        i = j
    return out


def tail_cells(tl):
    out = []
    for t in tl:
        out += [0] + [1] * t
    return out


def tail_blocks(cells):
    """The blocks of a tail `0 1^t1 0 1^t2 ...` (a block may be empty)."""
    s = "".join(map(str, cells))
    if not s:
        return ()
    assert s[0] == "0", cells
    return tuple(len(x) for x in s[1:].split("0"))


def nextps(m, tl, maxsteps=3 * 10 ** 7):
    """Run the machine from PS(m, tl) to the next phase start: (m', tail') or ('halt', steps)."""
    pad = 200000
    cells = [0] + [1] * m + tail_cells(tl)
    tape = [0] * pad + cells + [0] * 1000
    pos, st, lo, hi = pad, 5, pad, pad + len(cells) - 1
    for i in range(maxsteps):
        t = T[(st, tape[pos])]
        if t is None:
            return ("halt", i)
        tape[pos] = t[0]
        pos += t[1]
        st = t[2]
        hi = max(hi, pos)
        if pos < lo:
            lo = pos
            assert pos > 5
            if st == 5:
                r = rle(tape[lo:hi + 1])
                if r[0] == (0, 1) and r[1][0] == 1:
                    rest = tape[lo + 1 + r[1][1]:hi + 1]
                    while rest and rest[-1] == 0:
                        rest.pop()
                    return (r[1][1], tail_blocks(rest), i + 1)
    raise RuntimeError("no phase end")


_cache = {}


def phase(m, tl):
    key = (m % 3, tuple(tl))
    if key not in _cache:
        base = 3 * (10 + 3 * sum(tl) + 3 * len(tl)) + m % 3
        res = [nextps(b, tl) for b in (base, base + 3, base + 6)]
        if any(x[0] == "halt" for x in res):
            _cache[key] = ("halt", [x[:2] for x in res])
        else:
            assert len({x[1] for x in res}) == 1
            a = Fraction(res[1][0] - res[0][0], 3)
            assert a == Fraction(8, 3) and res[2][0] == res[0][0] + 8 * 2
            _cache[key] = ("lin", base, res[0][0], res[0][1])
    v = _cache[key]
    if v[0] == "halt":
        return v
    _, base, img, ntl = v
    return (img + 8 * (m - base) // 3, ntl)


def main():
    sys.set_int_max_str_digits(0)
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    for (_, m, tl), (_, m2, tl2) in zip(BLANK, BLANK[1:]):
        assert phase(m, tl) == (m2, tl2)
        if m < 5000:
            assert nextps(m, tl)[:2] == (m2, tl2)
    print(f"phase() and the machine agree on the {len(BLANK) - 1} phases from blank tape to step {BLANK[-1][0]}")
    halts = []
    for L in range(0, 4):
        for tl in itertools.product(range(1, 9), repeat=L):
            for r in range(3):
                x = nextps(3 * (10 + 3 * sum(tl) + 3 * L) + r, tl)
                if x[0] == "halt":
                    halts.append((tl, r))
    print("tails (up to 3 blocks of 1..8) and residues M mod 3 that halt:", halts)
    m, tl, big, counts = 9, (), (), {}
    for i in range(n):
        r = phase(m, tl)
        if r[0] == "halt":
            print(f"HALT in phase {i}: M mod 3 = {m % 3}, tail {tl}")
            return
        m, tl = r
        counts[len(tl)] = counts.get(len(tl), 0) + 1
        if sum(tl) + len(tl) > sum(big) + len(big):
            big = tl
            print(f"  phase {i + 1}: tail {list(tl)} (M has {len(str(m))} digits)")
    print(f"no halt in {n} phases; M has {len(str(m))} digits; phases by number of tail blocks: {sorted(counts.items())}")


if __name__ == "__main__":
    main()
