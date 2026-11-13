"""Exact round map of 1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA on lists of blocks.

A left-end tape  E> 0 1 a^x0 110 a^x1 110 ... 110 a^xk  (a = 01) is the list [x0, ..., xk] (zero blocks allowed: the
separator 110110 of the README is an empty block between two separators).

`closed(bl)`: the round in closed form (halving sweep with a carry, then drains), valid when no block met in halving
mode is small; returns None otherwise.
`nxt(bl)`: the round for every list, by exact extrapolation: the round is affine in every block larger than T once
its parity is fixed, so blocks above T are cut down to T or T+1 (same parity), the cut-down tape and the tapes with one
block two larger are run on the plain machine (direct.py), and the result is extended linearly.  Results for a
cut-down tape are cached.  Returns a list, 'halt', or raises on a tape outside the family.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from direct import rnd

T = 16
_cache = {}


def closed(bl):
    k = len(bl) - 1
    groups = []
    i = 0
    dsep = False
    while True:
        x = bl[i]
        last = i == k
        cont = (x % 2 == 1) if i == 0 else (x % 2 == 0)
        if not last:
            if cont:
                if x < (5 if i == 0 else 6):
                    return None
                groups.append((x - 5) // 2 if i == 0 else x // 2 - 3)
                i += 1
                continue
            m = x // 2 - 2 if i == 0 else (x - 5) // 2
            if m < 0:
                return None
            groups.append(m)
            R = [bl[i + 1] + 5] + [y + 1 for y in bl[i + 2:]]
            break
        if i == 0:
            if x % 2:
                m, R = (x - 1) // 2, [1]
            else:
                m, R, dsep = x // 2 - 2, [2, 1], True
        elif x % 2 == 0:
            m, R = x // 2 - 1, [1]
        else:
            m, R, dsep = (x - 5) // 2, [2, 1], True
        if m < 0:
            return None
        groups.append(m)
        break
    for gi in range(len(groups) - 1, -1, -1):
        m = groups[gi]
        R[0] += m
        R[-1] += 2 * m
        if gi > 0:
            R[0] += 4
            R[-1] += 2
            R = [2] + R
        else:
            R[-1] += 2
    if len(R) == 1:
        return [R[0] + 1]
    return [r - 1 for r in R[:-1]] + ([0] if dsep else []) + [R[-1] + 1]


def _base(key):
    if key in _cache:
        return _cache[key]
    r0 = rnd(list(key), 10 ** 8)[0]
    if not isinstance(r0, list):
        res = (r0, None)
    else:
        grads = {}
        for i, v in enumerate(key):
            if v >= T:
                k2 = list(key)
                k2[i] += 2
                r1 = rnd(k2, 10 ** 8)[0]
                k2[i] += 2
                r2 = rnd(k2, 10 ** 8)[0]
                assert isinstance(r1, list) and len(r1) == len(r0), (key, r0, r1)
                g = [b - a for a, b in zip(r0, r1)]
                assert g == [b - a for a, b in zip(r1, r2)], (key, r0, r1, r2)
                grads[i] = g
        res = (r0, grads)
    _cache[key] = res
    return res


def nxt(bl):
    key = tuple(x if x < T else T + (x - T) % 2 for x in bl)
    r0, grads = _base(key)
    if grads is None:
        if r0 == 'halt':
            return 'halt'
        raise ValueError(f'outside the family: {bl} -> {r0}')
    out = list(r0)
    for i, g in grads.items():
        d = (bl[i] - key[i]) // 2
        for j, c in enumerate(g):
            out[j] += c * d
    return out
