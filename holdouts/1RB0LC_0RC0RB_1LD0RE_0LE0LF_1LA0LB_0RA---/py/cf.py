"""Closed form of a clean visit to a list of plain blocks (frame A), the recursion of lean/Family.lean solved.

A visit to l = [b1, ..., bk] is clean (`clean`) when b1 is odd, the other blocks are even, and, for k >= 2,
b1 >= 7, b_i >= 2 + 18*5^(i-2) for 2 <= i <= k-1 and bk >= 2.  Then it leaves the blocks
    go(l) = l + (-5, -18, -90, ..., -18*5^(k-3), +12*5^(k-2))     (k >= 2),   go([b]) = [b+1]
and takes  steps(l) = sum_i 5^i b_i + K_k  machine steps (K_1 = 9, K_2 = 265, K_3 = 4245, ...), from the head in
A on the 0 in front of the blocks to the head in E on the same cell (one more step to leave it).
`python3 cf.py` checks all of this against the recursive definitions (`rec_*`, the Lean `go`/`goT`/`clean`).
"""
from functools import lru_cache


def eff(k):
    if k == 1:
        return [1]
    return [-5] + [-18 * 5 ** i for i in range(k - 2)] + [12 * 5 ** (k - 2)]


def clean(l):
    k = len(l)
    if k == 0 or l[0] % 2 != 1:
        return False
    if k == 1:
        return True
    if l[0] < 7 or l[-1] < 2:
        return False
    for i in range(1, k):
        if l[i] % 2:
            return False
    for i in range(1, k - 1):
        if l[i] < 2 + 18 * 5 ** (i - 1):
            return False
    return True


def go(l):
    return [b + e for b, e in zip(l, eff(len(l)))]


def bump(d, l):
    return [l[0] + d] + list(l[1:])


@lru_cache(maxsize=None)
def K(k):
    """the constant of the step count, from the recursion goT(b::c::bs) = 5b + 55 + sum of the five inner visits"""
    if k == 1:
        return 9
    # inner lists of a visit to (b, c, ...) relative to the values: l0 = (c+1, ...), l_{t+1} = bump(d, go(l_t))
    # sum over t of steps(l_t) = sum_t (sum_i 5^(i+1) l_t[i] + K(k-1)); l_t[i] = L[i] + shift_t[i]
    shifts = [[1] + [0] * (k - 2)]
    for d in (3, 1, 1, 1):
        s = shifts[-1]
        e = eff(k - 1)
        shifts.append([s[0] + e[0] + d] + [s[i] + e[i] for i in range(1, k - 1)])
    const = 55 + 5 * K(k - 1)
    for s in shifts:
        const += sum(5 ** (i + 1) * s[i] for i in range(k - 1))
    return const


def steps(l):
    """machine steps of a clean visit, head on its start cell at both ends (A before, E after)"""
    k = len(l)
    if k == 1:
        return 5 * l[0] + 9
    # 5*b1 + 55 + sum_t steps(l_t), l_t from (b2+1, b3, ...), five inner visits of total weight 5 each
    return sum(5 ** (i + 1) * l[i] for i in range(k)) + K(k)


# ---------------------------------------------------------------- the recursive definitions (as in Lean)
def rec_go(l):
    if len(l) == 1:
        return [l[0] + 1]
    b, c, bs = l[0], l[1], list(l[2:])
    l0 = [c + 1] + bs
    l1 = bump(3, rec_go(l0)); l2 = bump(1, rec_go(l1)); l3 = bump(1, rec_go(l2)); l4 = bump(1, rec_go(l3))
    return [b - 5] + rec_go(l4)


def rec_goT(l):
    if len(l) == 1:
        return 5 * l[0] + 9
    b, c, bs = l[0], l[1], list(l[2:])
    l0 = [c + 1] + bs
    l1 = bump(3, rec_go(l0)); l2 = bump(1, rec_go(l1)); l3 = bump(1, rec_go(l2)); l4 = bump(1, rec_go(l3))
    return (3 * b + 6) + rec_goT(l0) + 9 + rec_goT(l1) + 15 + rec_goT(l2) + 15 + rec_goT(l3) + 15 + rec_goT(l4) + (2 * b - 5)


def rec_clean(l):
    if len(l) == 0:
        return False
    if len(l) == 1:
        return l[0] % 2 == 1
    b, c, bs = l[0], l[1], list(l[2:])
    if not (b % 2 == 1 and b >= 7 and c >= 1):
        return False
    cur = [c + 1] + bs
    for d in (3, 1, 1, 1, None):
        if not rec_clean(cur):
            return False
        if d is not None:
            cur = bump(d, rec_go(cur))
    return True


if __name__ == "__main__":
    import random
    random.seed(7)
    n = bad = 0
    for _ in range(4000):
        k = random.randint(1, 5)
        cap = [12, 40, 130, 600, 3000]
        l = [random.randrange(0, cap[i]) for i in range(k)]
        if random.random() < 0.7:     # mostly near-clean lists
            l[0] |= 1
            for i in range(1, k):
                l[i] &= ~1
        a, b = rec_clean(l), clean(l)
        if a != b:
            bad += 1
            print("clean differs", l, a, b)
        if a:
            n += 1
            assert rec_go(l) == go(l), l
            assert rec_goT(l) == steps(l), (l, rec_goT(l), steps(l))
    print("checked", n, "clean lists,", bad, "differences;", "K =", [K(k) for k in range(1, 8)])
