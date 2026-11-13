"""The phase model of 1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA, and the run from blank tape in it.

S_t(x, c): head in A on the first cell of `1^x (01)^2 1^6 (01)^c 1^t 0 1^2`, t = 3 or 6.

* step:  S_t(x, c+2) -> S_t(floor(3x/2) + 7, c)                 (checked by rules_check.py step)
* reset: from S_T(x, C), C = 2 or 1, the machine either halts or comes back to S_t'(x', c') with
         t' = 3 if C = 2 and t' = 6 if C = 1, x' in {4, 6}, c' = c0 + s*(x - x0) depending on x mod P,
         or to `1^1 (01)^2 1^3 (01)^c' ...`, which reaches S_t'(5, c'-2) (checked by rules_check.py reset).
  The table below was read off rules_check.py reset C T 200 (every x < 200 fits, except C=1, T=3, x=3).

usage: python3 model.py            the run from S_3(4, 4) (reached at step 388) through phase 2
       python3 model.py verify X   compare the reset table with direct simulation for x < X
       python3 model.py next X     compare the reset table with the map `next` proved in lean/Reset.lean, x < X,
                                   and count the terms of its orbit from (4, 4, 3) up to phase 3
"""
import sys
from fractions import Fraction as F

# (C, T): (period P, slope s, {x0 mod P: None (halt) or (x0, x', b, c0)})
RESET = {
    (2, 3): (8, F(9, 8), {0: (32, 1, 3, 45), 1: None, 2: (34, 4, 6, 46), 3: (35, 1, 3, 48), 4: (36, 6, 6, 46),
                          5: (37, 4, 6, 49), 6: None, 7: (39, 6, 6, 49)}),
    (2, 6): (8, F(9, 8), {0: (32, 6, 6, 43), 1: (33, 4, 6, 46), 2: None, 3: (35, 6, 6, 46), 4: (36, 1, 3, 51),
                          5: None, 6: (38, 4, 6, 52), 7: (39, 1, 3, 54)}),
    (1, 3): (4, F(3, 4), {0: (32, 4, 6, 26), 1: (33, 1, 3, 28), 2: None, 3: (35, 6, 6, 26)}),
    (1, 6): (16, F(27, 16), {0: None, 1: (33, 4, 6, 68), 2: (34, 6, 6, 68), 3: (35, 4, 6, 71), 4: (36, 6, 6, 71),
                             5: (37, 1, 3, 76), 6: (38, 4, 6, 77), 7: (39, 1, 3, 79), 8: (40, 4, 6, 80), 9: None,
                             10: (42, 1, 3, 85), 11: None, 12: (44, 1, 3, 88), 13: (45, 6, 6, 86), 14: None,
                             15: (47, 6, 6, 89)}),
}


def reset(x, c, t):
    """The start after the reset from S_t(x, c), c in {1, 2}, as (x', c', t'), or None for a halt."""
    p, s, tab = RESET[(c, t)]
    e = tab[x % p]
    if e is None:
        return None
    x0, x1, b, c0 = e
    c1 = c0 + s * (x - x0)
    assert c1.denominator == 1
    c1 = int(c1)
    t1 = 3 if c == 2 else 6
    return (x1, c1, t1) if b == 6 else (5, c1 - 2, t1)


def verify(xmax):
    from rules_check import next_start
    bad = 0
    for (c, t), (p, s, tab) in RESET.items():
        for x in range(4, xmax):
            body = f"(01)^{c} " if c > 1 else "0 1 "
            got = next_start(f"1^{x} (01)^2 1^6 {body}1^{t} 0 1^2", c + 3)
            e = tab[x % p]
            if e is None:
                ok = got[0] == "HALT"
            else:
                ok = got[:2] == (e[1], e[2]) and got[2] == e[3] + s * (x - e[0])
            bad += not ok
            if not ok:
                print("mismatch", c, t, x, got, e)
    print("reset table:", bad, "mismatches")


def next_map(x, c, six):
    """`next` of lean/Reset.lean: the phase configuration after Ph(x, c, t), t = 6 if six else 3, or None."""
    t = 6 if six else 3
    if c >= 2:
        return (3 * x // 2 + 7, c - 2, six)
    if c == 0:
        b = 3 * (x // 2) + 7 + t
        if x % 2 == 0:
            return None if b % 2 == 0 else (4, (b - 5) // 2, False)
        return (6, (b - 8) // 2, False) if b % 2 == 0 else (5, (b - 5) // 2, False)
    if not six:
        b = 3 * (x // 2) + 7
        if x % 2 == 0:
            return None if b % 2 == 0 else (4, (b - 3) // 2, True)
        return (6, (b - 6) // 2, True) if b % 2 == 0 else (5, (b - 3) // 2, True)
    y = 3 * (x // 2) + 7 + x % 2
    return (3 * y // 2 + 4, 1, False)


def check_next(xmax):
    """The reset table from S_t(x, C) against `next`: from C = 2 one step and the c = 0 reset; from C = 1, t = 6
    the reset, the short phase and the c = 1, t = 3 reset."""
    bad = 0
    for (c, t) in RESET:
        for x in range(4, xmax):
            st = next_map(x, c, t == 6)
            if st is not None and st[1] in (0, 1) and (c, t) != (1, 3):
                st = next_map(*st)
            got = None if st is None else (st[0], st[1], 6 if st[2] else 3)
            if got != reset(x, c, t):
                bad += 1
                print("mismatch", c, t, x, got, reset(x, c, t))
    print("next against the reset table:", bad, "mismatches")
    st, i = (4, 4, False), 0
    while st is not None and st[1] < 10 ** 6:
        st, i = next_map(*st), i + 1
    print(f"orbit term {i}: S_{6 if st[2] else 3}({st[0]}, c), c with {len(str(st[1]))} digits, c odd: {st[1] % 2 == 1}")


def main(argv):
    if argv and argv[0] == "verify":
        verify(int(argv[1]))
        return
    if argv and argv[0] == "next":
        check_next(int(argv[1]))
        return
    x, c, t = 4, 4, 3
    for ph in range(4):
        print(f"phase {ph}: start S_{t}({x}, {show(c)})")
        if c > 10 ** 6:
            k = (c - 1) // 2
            print(f"  c is odd, so the phase ends at S_{t}(y, 1) after (c-1)/2 = {show(k)} steps, and it halts iff "
                  f"y = 2 mod 4 (table (1, {t})). y has about {show(int(0.176 * k))} digits: not computable.")
            return
        n = 0
        while c >= 3:
            x, c, n = 3 * x // 2 + 7, c - 2, n + 1
        print(f"  {n} steps, end S_{t}(x, {c}) with x = {show(x)}, x mod 16 = {x % 16}")
        r = reset(x, c, t)
        if r is None:
            print("  HALT")
            return
        x, c, t = r
        print("  no halt at this reset")


def show(n):
    s = str(n)
    return s if len(s) < 16 else f"{s[:8]}...{s[-4:]} ({len(s)} digits)"


if __name__ == "__main__":
    main(sys.argv[1:])
