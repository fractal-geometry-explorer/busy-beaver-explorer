"""The phase map of 1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD as proved in `lean/Phase.lean` and `lean/Orbit.lean`.

A transcription, line for line, of the Lean definitions `astep`, `arun`, `overflowStart`, `phase` (same names, same
cases, same fuel), so that it can be run far and compared with the machine and with the older trusted map
`macro.py`.

A post-event configuration is (d, M, Y): the bit string bitsOf M Y (lowest bit nearest the head) and the counter
0^d 1.  In the README's event terms X = Y - 2, j = d + 1, N = 3d + 1.

usage: python3 phasemap.py machine MMAX     every configuration (d <= M-1, Y < 2^M) whose phase overflows, M <= MMAX:
                                           the map against the machine run to its next post-event configuration
       python3 phasemap.py macro K          the first K overflows of the orbit against macro.py (the README map)
       python3 phasemap.py stuck MMAX       every (d, M, Y), M <= MMAX, where the map is stuck
       python3 phasemap.py orbit K          iterate K overflows, print each (d, M, Y mod 10^9)
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


def bitsOf(w, v):
    return [(v >> i) & 1 == 1 for i in range(w)]


def leadOnes(H):
    s = 0
    while s < len(H) and H[s]:
        s += 1
    return s


# Res: ("next", s) | ("done", d, w, v) | ("stuck",);  s = (w, v, l, c, k, H)
def astep(s):
    w, v, l, c, k, H = s
    if not H:
        if l == 0:
            return ("done", 0, w, v + 2) if v + 2 < 2 ** (w + 1) else ("stuck",)
        return ("done", l - 1, w, v) if c == 2 ** (l - 1) else ("stuck",)
    h, H1 = H[0], H[1:]
    if c + 1 < 2 ** l:
        n = 2 ** l - 1 - c
        return ("next", (w, v + 2 * n, l, 2 ** l - 1, k, H)) if v + 2 * n < 2 ** (w + 1) else ("stuck",)
    if c == 2 ** l - 1:
        if not h:
            return ("next", (w, v + 2, l + 1, 2 ** l, k, H1)) if v + 2 < 2 ** (w + 1) else ("stuck",)
        if k:
            if l % 2 == 0:
                return ("next", (w + 3 * (l // 2) + 1, 2 ** (3 * (l // 2)) * (1 + 2 * v), 0, 0, False, H1))
            return ("next", (w + 3 * (l // 2) + 3, 1 + 2 ** (3 * (l // 2) + 2) * (1 + 2 * v), 0, 0, True, H1))
        s1 = leadOnes(H1)
        if v + 2 < 2 ** (w + 1):
            return ("next", (w, v + 2, l + s1 + 2, 2 ** (l + s1 + 1), False, H1[s1 + 1:]))
        return ("stuck",)
    return ("stuck",)


def arun(n, s):
    for _ in range(n):
        r = astep(s)
        if r[0] != "next":
            return r
        s = r[1]
    return ("stuck",)


def fuel(d):
    return 2 * d + 12


def overflowStart(d, M, Y):
    i0 = (2 ** M - 2 + Y % 2 - Y) // 2
    if Y % 2 == 1:
        return (M - 1, 0, 0, 0, True, [False] + bitsOf(d + 2, 2 ** d + i0 + 1))
    return (M, 1, 0, 0, False, bitsOf(d + 2, 2 ** d + i0 + 1))


def phase(d, M, Y):
    if M == 0 or 2 ** M <= Y:
        return None
    if Y + 2 ** (d + 1) < 2 ** M:
        return (d + 1, M, Y + 2 ** (d + 1))
    r = arun(fuel(d), overflowStart(d, M, Y))
    if r[0] == "done":
        _, d2, w2, v2 = r
        return None if (d2 == d and w2 + 1 == M) else (d2, w2 + 1, v2)
    return None


def overflows(k):
    """The first k overflow phases of the orbit from (0, 2, 2): yields (index, before, after)."""
    st, i, n = (0, 2, 2), 0, 0
    while n < k:
        nx = phase(*st)
        if nx is None:
            yield i, st, None
            return
        if not (st[2] + 2 ** (st[0] + 1) < 2 ** st[1]):
            yield i, st, nx
            n += 1
        st, i = nx, i + 1


def check_machine(mmax):
    import macro
    from bitmodel import from_bits
    agree = differ = halt_ok = halt_bad = 0
    for M in range(2, mmax + 1):
        for d in range(0, M):
            for Y in range(2 ** M):
                if Y + 2 ** (d + 1) < 2 ** M:
                    continue
                X = Y - 2
                if X < 0:
                    continue        # never at an event (the string is at least 2 at every P configuration)
                got = macro.first_event(from_bits([int(c) for c in format(X, f"0{M}b")]), 3 * (d + 1) - 2)
                if got != "HALT" and got[1] == M and got[0] >= 2 ** M - 2:
                    # the overflowing count is the one through this event (its string has no room for the +2 of
                    # the next post-event configuration): run on to the event after it
                    X2, M2, N2 = got
                    got = macro.first_event(from_bits([int(c) for c in format(X2, f"0{M2}b")]), N2)
                exp = phase(d, M, Y)
                if got == "HALT" or exp is None:
                    if got == "HALT" and exp is None:
                        halt_ok += 1
                    else:
                        halt_bad += 1
                        print("  halt mismatch", d, M, Y, got, exp)
                    continue
                if (exp[2] - 2, exp[1], 3 * exp[0] + 1) == got:
                    agree += 1
                else:
                    differ += 1
                    print("  differ", d, M, Y, got, exp)
    print(f"M <= {mmax}: {agree} overflows agree with the machine, {differ} differ; "
          f"{halt_ok} halt where the map is stuck, {halt_bad} mismatches")


if __name__ == "__main__":
    what, n = sys.argv[1], int(sys.argv[2])
    if what == "machine":
        check_machine(n)
    elif what == "macro":
        import macro
        mac = [new for (_, _, _, _, new) in macro.phases(0, 2, 1, n)]
        ours = [a for (_, _, a) in overflows(n)]
        bad = sum(1 for a, b in zip(ours, mac) if a is None or b is None or (a[2] - 2, a[1], 3 * a[0] + 1) != b)
        print(f"{len(ours)} overflows of the orbit against macro.py: {bad} differ; last M = {ours[-1][1]}")
    elif what == "stuck":
        out = []
        for M in range(1, n + 1):
            for d in range(0, M + 2):
                for Y in range(2 ** M):
                    if phase(d, M, Y) is None:
                        out.append((d, M, Y))
        fam = [(d, M, Y) for (d, M, Y) in out if d == M - 2 and Y == 2 ** (M - 1) + 1]
        rest = [(d, M, Y) for (d, M, Y) in out if (d, M, Y) not in fam]
        print(f"stuck at {len(out)} configurations with M <= {n}: {len(fam)} are (M-2, M, 2^(M-1)+1); the others "
              f"have Y <= 1 or d >= M-1: {all(Y <= 1 or d >= M - 1 for (d, M, Y) in rest)}")
    elif what == "orbit":
        for i, a, b in overflows(n):
            print(i, a[0], a[1], b if b is None else (b[0], b[1], b[2] % 10 ** 9))
