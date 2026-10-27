"""Halting full-pass landings from the halting classes of pass starts with R >= 178 (untrusted, for looking).

Reads the output of `lean/HaltClasses.lean search pow j ...` (lines `close R=.. D=.. a=.. b=b0+[0, M] rounds=..`), one or
more scales j, with W - b = D = 2^(j+2) - 2R - 22 (the route on which the end is met off the loop's chain at 2^j - 2).

Within a scale the class of the middle wall moves affinely with R in steps of 8, separately for R = 2 and R = 6 (mod 8):
for R = R0 + 8s, b = beta + delta*s (mod M).  The lane is fitted from R0, R0 + 8 and R0 + 16 and checked on the third
(an extrapolation beyond them: check any landing it lists on the model, `HaltClasses.lean land`).

A full pass from a pass start with every gap at least 448 lands at a = W/2 - D + R + 3 (the plane 2(b - a) = W - 2R - 6),
W = 0 (mod 4), with 4D - 8R + 63 <= W <= (64D - 144R - 375)/15, which is empty for R > 2^(j-1) - 44.  For each lane
this lists the points of that window in the lane's class: halting landings, if the lane is right.

usage: python3 halt_lanes.py classes.txt [max listed per lane]
"""
import math
import re
import sys

import numpy as np


def classes(path):
    rows = {}
    for line in open(path):
        m = re.match(r'close R=(\d+) D=(\d+) a=.*? b=(\d+)\+\[0, (\d+)\] rounds=(\d+)', line)
        if not m:
            continue
        R, D, b, M, r = map(int, m.groups())
        j = int(math.log2(D + 2 * R + 22)) - 2
        if D + 2 * R + 22 != 2 ** (j + 2):
            continue
        rows.setdefault(j, {})[R] = (b, M, r)
    return rows


def fit(cl, R0):
    """beta, delta, M for R = R0 + 8s, from R0, R0 + 8 and R0 + 16, and whether the third agrees."""
    if not all(R in cl for R in (R0, R0 + 8, R0 + 16)):
        return None
    M = min(cl[R][1] for R in (R0, R0 + 8, R0 + 16))
    b0, b1, b2 = (cl[R][0] % M for R in (R0, R0 + 8, R0 + 16))
    d = (b1 - b0) % M
    return b0, d, M, (b0 + 2 * d) % M == b2


def landings(j, R0, beta, delta, M, nmax):
    out = []
    mask = np.uint64(M - 1)
    chunk = 1 << 22
    Rmax = 2 ** (j - 1) - 44
    s0 = 0
    while R0 + 8 * s0 <= Rmax and len(out) < nmax:
        s = np.arange(s0, s0 + chunk, dtype=np.int64)
        R = R0 + 8 * s
        s, R = s[R <= Rmax], R[R <= Rmax]
        if len(s) == 0:
            break
        D = 2 ** (j + 2) - 2 * R - 22
        Wlo = 4 * D - 8 * R + 63
        Whi = (64 * D - 144 * R - 375) // 15
        cls = (np.uint64(beta) + np.uint64(delta) * s.astype(np.uint64)) & mask
        W = Wlo + ((cls + (D - Wlo).astype(np.uint64)) & mask).astype(np.int64)  # the least W >= Wlo in the class
        for i in np.nonzero((W <= Whi) & (W % 4 == 0))[0][: nmax - len(out)]:
            Ri, Di, Wi = int(R[i]), int(D[i]), int(W[i])
            out.append((Wi // 2 - Di + Ri + 3, Wi - Di, Wi, Ri))
        s0 += chunk
    return out


if __name__ == '__main__':
    rows = classes(sys.argv[1])
    nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    for j in sorted(rows):
        for R0 in (178, 182):
            f = fit(rows[j], R0)
            if f is None:
                continue
            beta, delta, M, ok = f
            hs = landings(j, R0, beta, delta, M, nmax) if ok else []
            print(f"j={j} R={R0}+8s: b = {beta} + {delta}s (mod 2^{M.bit_length() - 1}), lane checked {ok}, "
                  f"landings {len(hs)}")
            for a, b, W, R in hs:
                print(f"  a={a} b={b} W={W} R={R}")
