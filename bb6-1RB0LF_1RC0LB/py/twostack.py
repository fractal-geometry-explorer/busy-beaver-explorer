"""The macro machine (py/macro.py, lean/Macro.lean) rewritten as two stacks and a cursor.

Write every value of an F configuration in one row, left to right: the stack from the bottom up, a 0 for the F head,
then the word segments and the last segment.  Give each entry a gap: 0 for the stack entries and the head, n = g - 1
for a word segment, and "end" for the last segment.  Left of the row stand infinitely many entries -1 with gap 0.
The cursor is the first entry whose gap is not 0; everything left of it is a stack L of plain numbers, everything
right of it a stack R of (value, gap) pairs.

Two rules give the next F configuration (the B pass in between is folded in):

    R1  gap n >= 1 or end:   a, b, x<n>      ->  0, (a+2)<b>, x<n-2>        (end stays end)
    R2  gap n = -1:          a, x<-1>, y<m>  ->  0, (a+2)<x-2>, (y-1)<m>    needs x >= 1 and y >= 1
                             a, x<-1>, 0<end> -> 0, (a+2)<end>

a and b are the two entries left of the cursor (from the -1 entries when L is short).  An entry whose new gap is 0
joins L.  R2 is the rule for two 1s side by side; it is the only place a value goes down, and the only place the
macro machine can get stuck.

usage:
  python3 py/twostack.py check T     T macro steps from M0: compare the two-stack run with the macro machine at every
                                     F configuration
  python3 py/twostack.py show T [FROM]
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from macro import M0, mstep  # noqa: E402

END = None


def from_macro(c):
    """The row of an F configuration: a list of [value, gap], leading [-1, 0] entries dropped."""
    assert c[0] == "F"
    _, S, ws, mt = c
    z = [[s, 0] for s in reversed(S)] + [[0, 0]]
    z += [[m, g - 1] for m, g in ws]
    z.append([mt, END])
    return norm(z)


def norm(z):
    i = 0
    while i < len(z) - 1 and z[i] == [-1, 0]:
        i += 1
    return z[i:]


def cursor(z):
    i = 0
    while z[i][1] == 0:
        i += 1
    return i


def zstep(z):
    """One step of the two-stack form (= one F pass and the B pass after it), or None where R2 does not apply."""
    z = [list(e) for e in z]
    i = cursor(z)
    while i < 2:
        z.insert(0, [-1, 0])
        i += 1
    x, n = z[i]
    if n is END or n >= 1:
        a, b = z[i - 2][0], z[i - 1][0]
        z[i - 2] = [0, 0]
        z[i - 1] = [a + 2, b]
        if n is not END:
            z[i][1] = n - 2
        return norm(z)
    if x < 1:
        return None
    a = z[i - 1][0]
    y, m = z[i + 1]
    if m is END and y == 0:
        return norm(z[:i - 1] + [[0, 0], [a + 2, END]])
    if y < 1:
        return None
    z[i - 1] = [0, 0]
    z[i] = [a + 2, x - 2]
    z[i + 1] = [y - 1, m]
    return norm(z)


def show(z):
    i = cursor(z)
    left = " ".join(str(v) for v, _ in z[:i])
    right = " ".join(f"{v}<{'end' if g is END else g}>" for v, g in z[i:])
    return f"{left} | {right}"


def check(T):
    """T macro steps from M0; returns (F configurations compared, mismatches)."""
    c, z, n, bad = M0, None, 0, 0
    for _ in range(T):
        if c[0] == "F":
            if z is not None:
                z = zstep(z)
                n += 1
                if z != from_macro(c):
                    bad += 1
            z = from_macro(c)
        c = mstep(c)
    return n, bad


def main(argv):
    if argv[0] == "check":
        n, bad = check(int(argv[1]))
        print(f"F configurations compared {n}, mismatches {bad}")
    elif argv[0] == "show":
        T = int(argv[1])
        a = int(argv[2]) if len(argv) > 2 else 0
        c = M0
        while c[0] != "F":
            c = mstep(c)
        z = from_macro(c)
        for t in range(T):
            if t >= a:
                print(t, show(z))
            z = zstep(z)


if __name__ == "__main__":
    main(sys.argv[1:])
