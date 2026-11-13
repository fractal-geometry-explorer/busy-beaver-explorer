"""The block map of 1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA: the machine as a rewriting system on lists of blocks of 1s.

`blk [a, b, c, ...]` is the tape `1^a 0 1^b 0 1^c 0 ...` (then blank; an empty list is blank tape), read away from
the head on either side.  A frame is a state and two block lists L, R:

    E L R :  blk(L) E> 0 blk(R)        C L R :  blk(L) C> 0 blk(R)
    B L R :  blk(L) B> blk(R)          F L R :  blk(L) F> blk(R)

`nxt` is the map of `lean/Blocks.lean` (same cases, same order), proved there for all block lists; it is undefined
(None) exactly at the three halting cases

    C (2 :: L) (r+1 :: R)      0 1 1 C> 0 1
    B (1 :: L) (r+3 :: R)      0 1 B> 1 1 1
    F L (r+2 :: R)             F> 1 1

usage (from the repository root):
  python3 holdouts/1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA/py/blockmap.py check STEPS   compare with the machine for STEPS steps
  python3 holdouts/1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA/py/blockmap.py run K         iterate the map K times, print statistics
  python3 holdouts/1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA/py/blockmap.py show K        print the first K frames
"""
import sys

M = "1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA"


def un(X):
    """head and tail of a block list; the empty list is blank tape = an empty block before blank tape."""
    return (X[0], X[1:]) if X else (0, ())


def nxt2(f):
    """(next frame, machine steps it takes), or None at a critical frame."""
    q, L, R = f
    if q == "E":
        i, L1 = un(L); m, R1 = un(R)
        if m == 0:
            return ("E", L1, (i + 1,) + R1), i + 3
        if m == 1:
            r, R2 = un(R1)
            return ("C", (r, i + 2) + L1, R2), r + 5
        return ("C", (m - 2, i + 2) + L1, R1), m + 7
    if q == "C":
        a, L1 = un(L); r, R1 = un(R)
        if a == 0:
            return ("C", (r + 1,) + L1, R1), r + 3
        if a == 1:
            b, L2 = un(L1)
            return ("E", L2, (b, 0, r + 1) + R1), b + 3
        if a == 2:
            if r >= 1:
                return None
            b, L2 = un(L1)
            return ("B", (b + 5,) + L2, R1), 8
        return ("C", (r + 1, a - 1) + L1, R1), r + 7
    if q == "B":
        a, L1 = un(L); r, R1 = un(R)
        if r == 0:
            s, R2 = un(R1)
            return ("C", (s, a) + L1, R2), s + 1
        if a == 0:
            b, L2 = un(L1)
            return ("E", L2, (b, 0, r - 1) + R1), b + 2
        if a == 1:
            b, L2 = un(L1)
            if r == 1:
                return ("F", (b + 4,) + L2, R1), 6
            if r == 2:
                return ("B", (b + 5,) + L2, R1), 7
            return None
        return ("C", (r - 1, a) + L1, R1), r + 4
    if q == "F":
        a, L1 = un(L); r, R1 = un(R)
        if r == 0:
            return ("F", (a + 1,) + L1, R1), 1
        if r == 1:
            return ("B", (a + 2,) + L1, R1), 2
        return None


def nxt(f):
    g = nxt2(f)
    return None if g is None else g[0]


START = ("B", (1,), ())     # after 1 step from blank tape


def cells(X):
    out = []
    for a in X:
        out += [1] * a + [0]
    while out and out[-1] == 0:
        out.pop()
    return out


def config(f):
    """(state, left cells nearest first, right cells from the head cell), trailing 0s dropped."""
    q, L, R = f
    r = cells(R)
    if q in "EC":
        r = [0] + r
        while r and r[-1] == 0:
            r.pop()
    return q, cells(L), r


def check(steps):
    T = {}
    for i, g in enumerate(M.split("_")):
        for b in (0, 1):
            w = g[3 * b:3 * b + 3]
            T[("ABCDEF"[i], b)] = None if w[0] == "-" else (int(w[0]), 1 if w[1] == "R" else -1, w[2])
    tape = {}; p = 0; q = "A"; lo = hi = 0
    f = START; want = config(f); nf = 0; due = 1
    for n in range(1, steps + 1):
        w, d, q2 = T[(q, tape.get(p, 0))]
        tape[p] = w; p += d; q = q2; lo = min(lo, p); hi = max(hi, p)
        if q == want[0]:
            l = [tape.get(i, 0) for i in range(p - 1, lo - 1, -1)]
            r = [tape.get(i, 0) for i in range(p, hi + 1)]
            while l and l[-1] == 0: l.pop()
            while r and r[-1] == 0: r.pop()
            if n == due and l == want[1] and r == want[2]:
                nf += 1; last = n
                f, c = nxt2(f); want = config(f); due = n + c
    print("machine steps", steps, ": followed", nf, "frames of the block map, each at the step the map says, the last at step", last)


if __name__ == "__main__":
    if len(sys.argv) != 3 or sys.argv[1] not in ("check", "run", "show"):
        sys.exit(__doc__)
    cmd, n = sys.argv[1], int(sys.argv[2])
    if cmd == "check":
        check(n)
    else:
        f = START; mx = 0; t = 1
        for k in range(n):
            if cmd == "show":
                print(k, t, f[0], list(f[1]), list(f[2]))
            g = nxt2(f)
            if g is None:
                print("critical frame after", k, "iterations, step", t, ":", f); break
            f, c = g; t += c; mx = max(mx, len(f[1]) + len(f[2]))
        else:
            print(n, "iterations =", t, "machine steps, no critical frame; most blocks on the tape:", mx, "; last frame", f[0], list(f[1])[:8], list(f[2])[:8])
