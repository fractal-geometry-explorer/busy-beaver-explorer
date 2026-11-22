"""Check the round-trip rule of README.md ("The round trip as a CA rule") on the run from blank tape.

usage (from the repository root):  python3 holdouts/1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---/py/ca_check.py [STEPS] [MACHINE ...]

Default: 2*10^7 steps of this machine and its five siblings.  Plain Python, about a million steps a second.

At each return of the head to the left end (after being more than 40 cells away) the tape is in group form: groups
1 (01)^(2k) separated by 000.  A group start (a 1 after 000) marks the letter s, every other 4th cell the letter c.
Letters are counted from the left end of the tape, on the grid the group starts lie on.  For each pair of
consecutive round trips the check is  z_before(n) = z_after(n) XOR z_after(n-1)  (z = 1 for s) at every letter n
that both words have, up to the right-end layer (the first group start off the grid, or the first irregular
group, and everything right of it).  Machines whose sweeps run the other way are mirrored first.
"""
import collections
import re
import sys

SIBLINGS = ['1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---', '1RB---_0RC0LA_1LD0RB_1LE0LB_1LF0LC_1LB1RE',
            '1RB---_0RC0LA_1LD0RB_1LE1LD_1LF0LC_1LB1RE', '1RB0LE_1RC0RE_1RD0RA_1RE1LC_0LA0RF_1LE---',
            '1RB0RD_1RC0RE_1RD1LB_0LE0RF_1RA0LD_1LD---', '1RB1RA_1RC0RE_1RD1LB_0LE0RF_1RA0LD_1LD---']
MIRRORED = {'1RB---_0RC0LA_1LD0RB_1LE0LB_1LF0LC_1LB1RE', '1RB---_0RC0LA_1LD0RB_1LE1LD_1LF0LC_1LB1RE'}
GROUP = re.compile(rb'\x01(\x00\x01)*\x00\x00\x00')


def parse(m, mirror=False):
    t = {}
    for s, part in enumerate(m.split("_")):
        for r in range(2):
            x = part[3 * r:3 * r + 3]
            d = 1 if x[1] == "R" else -1
            t[(s, r)] = None if x[2] == "-" else (int(x[0]), -d if mirror else d, ord(x[2]) - 65)
    return t


def snapshots(m, steps):
    """The tape (from the left end) at each return to the left end."""
    T = parse(m, m in MIRRORED)
    N = 1 << 23
    tape = bytearray(N)
    p = lo = hi = N // 2
    st, far = 0, False
    for k in range(steps):
        tr = T[(st, tape[p])]
        if tr is None:
            raise SystemExit(f"{m}: halts at step {k + 1}")
        tape[p], p, st = tr[0], p + tr[1], tr[2]
        if p < lo:
            lo = p
        if p > hi:
            hi = p
        if not far and p - lo > 40:
            far = True
        elif far and p <= lo + 6:
            far = False
            yield k + 1, bytes(tape[lo:hi + 1])


def letters(w):
    """z word (list of 0/1) on the grid of the group starts, from the first group start up to the right-end layer;
    and the offset of the first letter from the left end."""
    starts = [i for i in range(3, len(w)) if w[i] == 1 and w[i - 3:i] == b'\0\0\0']
    r = collections.Counter(i % 4 for i in starts).most_common(1)[0][0]
    i = next(i for i in starts if i % 4 == r)
    first = i
    z = []
    while True:
        g = GROUP.match(w, i)
        if not g or g.end() >= len(w) or w[g.end()] != 1:
            break
        n = (g.end() - i) // 4
        z += [1] + [0] * (n - 1)
        i = g.end()
    return z, first


def check(m, steps):
    prev = None
    trips = letters_checked = bad = 0
    off = collections.Counter()
    for k, w in snapshots(m, steps):
        z, first = letters(w)
        if prev is not None:
            pz, pfirst = prev
            # the left end moves one cell left each round trip and the grid one cell left with it: new letter n
            # sits one cell left of old letter n - d/4
            d = pfirst - first
            off[d] += 1
            if d % 4 == 0:
                s = -d // 4  # letter n of the new word is letter n + s of the old one
                for n in range(1, len(z)):
                    if 0 <= n + s < len(pz):
                        letters_checked += 1
                        bad += pz[n + s] != z[n] ^ z[n - 1]
                trips += 1
        prev = (z, first)
    return trips, letters_checked, bad, dict(off)


if __name__ == "__main__":
    steps = int(sys.argv[1]) if len(sys.argv) > 1 else 2 * 10 ** 7
    for m in sys.argv[2:] or SIBLINGS:
        trips, n, bad, off = check(m, steps)
        print(f"{m}: {trips} round trips, {n} letters checked, {bad} mismatches (shifts of the first group start: {off})")
