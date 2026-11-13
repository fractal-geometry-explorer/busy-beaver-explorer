#!/usr/bin/env python3
"""zones.py EDGE_R EDGE_L: the zones of 1RB0LD_0RC1RA_1LD1RC_1LE0RF_---1LA_1LF0LA beside its long run of one 51-cell word.

EDGE_R / EDGE_L are outputs of ../c/edge.c (the whole tape each time the head reaches a fresh cell on the right / on
the left). At the right end the tape is cut after the last two consecutive copies of w (any rotation); at the left
end, where the tape is written in another code, the word is found as the 51-cell period of the middle of the tape and
the tape is cut before the first two copies. Prints, for the right zone, the first visit from which it repeats with
a fixed period, and for the left zone how many different values it takes."""
import sys

W = '110111011101101101110111101111101111101111111011111'


def tapes(path):
    for line in open(path):
        f = line.split()
        if len(f) == 3:
            yield f[2].replace('[', '').replace(']', '')


def rotations(w):
    return {w[i:] + w[:i] for i in range(len(w))}


def right_zones(path):
    rots = rotations(W)
    out = []
    for t in tapes(path):
        best = max(((t.rfind(r * 2), r) for r in rots), default=(-1, None))
        out.append(t[best[0] + 2 * len(W):] if best[0] >= 0 else None)
    return out


def left_zones(path):
    ts = list(tapes(path))
    t = ts[-1]; mid = len(t) // 2
    p = next(p for p in range(1, 200) if all(t[i] == t[i + p] for i in range(mid, mid + 2000)))
    rots = rotations(t[mid:mid + p])
    out = []
    for t in ts:
        js = [j for j in (t.find(r * 2) for r in rots) if j >= 0]
        out.append(t[:min(js)] if js else None)
    return p, out


if __name__ == '__main__':
    z = right_zones(sys.argv[1])
    n = len(z)
    for per in range(1, 50):
        start = n - per
        while start - 1 >= 0 and z[start - 1 + per] == z[start - 1]:
            start -= 1
        if start < n - 2 * per:
            print(f'right zone: {n} visits; periodic with period {per} from visit {start + 1} on '
                  f'({len(set(z[start:]))} distinct values from there)')
            break
    else:
        print(f'right zone: {n} visits; no period below 50')
    if len(sys.argv) > 2:
        p, zl = left_zones(sys.argv[2])
        print(f'left zone: word period {p}; {len(zl)} visits, {len(set(zl))} distinct values')
