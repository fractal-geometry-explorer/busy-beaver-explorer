"""The pass map of the 1RB0LA_1RC--- family, checked against the machine.

usage (from the repository root):  python3 holdouts/<M>/py/passmap.py MACHINE STEPS [show N]

Machines 1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA, 1RB0LA_1RC---_0LD1RD_0RB0RE_0RF0LD_1LF0LA and
1RB1RF_0RC1RD_1LC1LA_0LE1RE_1RA0RB_---0LC.  Each time the head comes back to the solid block on the left (the wall),
the tape right of it is a list of blocks  1^(3k) 0  (k >= 1; k = 0 is an extra 0) and a tail  1^(t0 + 3j)  (t0 = 7,
or 6 for the third machine).  Write that as  k1 k2 ... kn Tj.  `step` below is the conjectured map from one wall
visit to the next; this script runs the C simulator (c/blkev.c, compiled into /tmp), reads every wall visit and
checks the map on each pair of consecutive visits.  Visits where the list touches the wall (the first entries) are
counted separately: there the wall itself takes part (see the README).
"""
import os, re, subprocess, sys, tempfile, collections

HERE = os.path.dirname(os.path.abspath(__file__))
CFG = {"1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA": ("D", 7),
       "1RB0LA_1RC---_0LD1RD_0RB0RE_0RF0LD_1LF0LA": ("D", 7),
       "1RB1RF_0RC1RD_1LC1LA_0LE1RE_1RA0RB_---0LC": ("E", 6)}


class Stuck(Exception):
    pass


def step(L, j):
    """One pass: (list, tail) -> (list, tail).  Stuck if the rule needs the wall."""
    if 0 not in L:                       # no empty block: the tail splits off, or an empty block is appended
        return (L + [j], 0) if j >= 1 else (L + [0], 0)
    i = L.index(0)                       # the first empty block is where the pass acts
    if i < 1:
        raise Stuck("empty block next to the wall")
    n, X = L[i - 1], (L[i + 1:], j)
    if n >= 2:                           # n 0 X  ->  (n-2) 1 f(X)
        Y = f(*X)
        return L[:i - 1] + [n - 2, 1] + Y[0], Y[1]
    if i < 2:
        raise Stuck("a 1 0 with the wall as a")
    a = L[i - 2]                         # a 1 0 X  ->  (a+2) X'   (X = 1 X')   or  a 1 0 T0 -> T(a+1)
    if X == ([], 0):
        return L[:i - 2], a + 1
    if not X[0] or X[0][0] != 1:
        raise Stuck("unexpected tail after a 1 0")
    return L[:i - 2] + [a + 2] + X[0][1:], X[1]


def f(Lx, j):
    """What the part after an empty block becomes: T0 -> 1 T0, and 1 Y -> 2 step(Y)."""
    if (Lx, j) == ([], 0):
        return [1], 0
    if not Lx or Lx[0] != 1:
        raise Stuck("unexpected word after an empty block")
    Y = step(Lx[1:], j)
    return [2] + Y[0], Y[1]


def parse(line, t0):
    """'STEPS WALL | 0 D>1 0 1^9 0 ... 1^7' -> (steps, wall, list, tail) or None if not of the expected shape."""
    a, b = line.split("|")
    steps, wall = map(int, a.split())
    toks = b.split()[2:]                 # drop '0' and the head cell 'D>1'
    L, j = [], None
    for i, t in enumerate(toks):
        m = re.fullmatch(r"([01])(?:\^(\d+))?", t)
        if not m:
            return None
        c, n = int(m.group(1)), int(m.group(2) or 1)
        last = i == len(toks) - 1
        if c == 1:
            if last:
                if n < t0 or (n - t0) % 3:
                    return None
                j = (n - t0) // 3
            elif n % 3:
                return None
            else:
                L.append(n // 3)
        else:
            L.extend([0] * (n - 1))
    if j is None:
        return None
    return steps, wall, L, j


def show(L, j):
    return " ".join(map(str, L)) + f" T{j}"


def main(argv):
    m, steps = argv[0], int(argv[1])
    st, t0 = CFG[m]
    exe = os.path.join(tempfile.gettempdir(), "bbx_blkev")
    subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(HERE, "..", "c", "blkev.c")], check=True)
    p = subprocess.Popen([exe, m, str(steps), st, "1", "1000"], stdout=subprocess.PIPE, text=True)
    prev, cnt = None, collections.Counter()
    shown = int(argv[3]) if len(argv) > 3 and argv[2] == "show" else 0
    for line in p.stdout:
        if line.startswith("HALT"):
            print(line.strip()); break
        ev = parse(line, t0)
        if ev is None:
            cnt["visits of another shape"] += 1; prev = None; continue
        if shown:
            print(ev[0], ev[1], show(ev[2], ev[3])); shown -= 1
        if prev is not None:
            try:
                got, seq = (prev[2], prev[3]), []
                for r in range(3):          # a pass can come back to the wall in another state, unseen here
                    got = step(*got); seq.append(got)
                    if got == (ev[2], ev[3]):
                        break
                if got == (ev[2], ev[3]):
                    cnt["visits that follow the map"] += 1
                    cnt[f"  after {len(seq)} pass(es) of the map"] += 1
                    if ev[1] - prev[1] != 3 * len(seq):
                        cnt["  of which the wall did not grow by 3 per pass"] += 1
                else:
                    cnt["mismatches"] += 1
                    if cnt["mismatches"] <= 5:
                        print("mismatch at", ev[0], ":", show(prev[2], prev[3]), "->", show(ev[2], ev[3]), "map:", show(*seq[0]))
            except Stuck as e:
                cnt["passes that reach the wall"] += 1
        prev = ev
    for k, v in cnt.items():
        print(f"{k}: {v}")
    if prev:
        print("last visit:", prev[0], "wall", prev[1], "list", show(prev[2], prev[3]))


if __name__ == "__main__":
    main(sys.argv[1:])
