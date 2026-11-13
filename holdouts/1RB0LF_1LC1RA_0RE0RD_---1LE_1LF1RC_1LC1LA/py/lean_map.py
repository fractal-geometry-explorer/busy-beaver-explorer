"""The map F of lean/Reset.lean, transcribed, and checked against the fitted map (m2map.G), the closed form of the
halting states (InH) and the machine itself.

usage: python3 py/lean_map.py N NSIM      (map vs m2map and InH for t < N; map vs direct simulation for t < NSIM)

States: ('z', t) is 1^t A> (a solid block of t ones, A on the blank cell after it), ('rs', d) is C> 0 1^(2d+4) at
the left end (the rounds of the odd reset starting over); None means the machine halts."""
import sys
from m2map import G as fitted
from check_map import next_z


def sweepv(x, y):
    """(10)^x 1^(2y+1) A> runs into 1^sweepv(x,y) A>."""
    return 2 * y + 1 + 3 * x if x % 2 == 0 else 2 * y + 3 * x + 3


def chain(a, d):
    """The rounds from C> 0 1 (01)^(a+1) 1^(2d+1)."""
    while True:
        if d == 0:
            return None
        if d < a:
            return ('z', sweepv(a - 1 - d, 2 * d + 2))
        if d == a:
            return ('z', 4 * a + 4)
        if d == a + 1:
            return ('rs', 2 * a + 3)
        a, d = 2 * a + 3, d - a - 2


SMALL = {0: ('z', 19), 1: ('z', 19), 2: ('z', 6), 3: None, 4: ('z', 7), 5: ('z', 20)}


def F(s):
    kind, v = s
    if kind == 'rs':
        return chain(1, v)
    if v in SMALL:
        return SMALL[v]
    if v % 2 == 0:
        return ('z', sweepv(v // 2 - 2, 3))
    return chain(1, (v + 3) // 2)


def in_h(s):
    """The closed form of the halting states (InH in lean/Reset.lean)."""
    kind, v = s
    k = 0
    while True:
        lhs, rhs = (v + 2 * k + 11, 2 ** (k + 3)) if kind == 'z' else (v + k + 4, 2 ** (k + 2))
        if lhs == rhs:
            return True
        if rhs > lhs:
            return False
        k += 1


def G(t):
    """F with the restarts followed: the next block 1^t' after 1^t, or None (halt)."""
    s = F(('z', t))
    while s is not None and s[0] == 'rs':
        s = F(s)
    return None if s is None else s[1]


if __name__ == '__main__':
    n, nsim = int(sys.argv[1]), int(sys.argv[2])
    bad = 0
    for t in range(2, n):
        if G(t) != fitted(t) and t >= 6:
            bad += 1; print('vs m2map', t, G(t), fitted(t))
        if (F(('z', t)) is None) != in_h(('z', t)):
            bad += 1; print('vs InH', t)
        if (F(('rs', t)) is None) != in_h(('rs', t)):
            bad += 1; print('vs InH rs', t)
    for t in range(2, nsim):
        s = F(('z', t))
        while s is not None and s[0] == 'rs':
            s = F(s)
        if (None if s is None else s[1]) != next_z(t):
            bad += 1; print('vs machine', t, s, next_z(t))
    print('checked: %d mismatches' % bad)
