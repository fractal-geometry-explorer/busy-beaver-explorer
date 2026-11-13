"""Check the macro map (amodel.py, the Python twin of `astep` in lean/Full.lean) against direct simulation: along
the accelerated run of hyb.py from blank tape, every irregular step (anomaly or collision) is simulated cell by
cell (c/trans.c) and compared with the map; also prints, for each anomaly, the word's number of bits B, the
counter's low part a and its number of bits k (the race needs a <= B - 1, see README).

usage: python3 check_amodel.py NTRANSIENTS
"""
import collections
import sys

from amodel import astep
from hyb import Nphi, comp, from_blank, jcoll, jump, transient

M = "1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---"


def to_wag(W, k, q, g, rest):
    a, P = comp(k, q)
    return list(W), a, [3 * p - 1 for p in P] + ([g] + rest if g is not None else [])


def main(n):
    st = from_blank(M)
    cnt = collections.Counter()
    bad = 0
    margins = []
    for e in range(n):
        W, k, q, g, rest, _ = st
        Ja, Jc = Nphi(W) // 2, jcoll(k, q, g)
        st = jump(st, Ja if Jc is None else min(Ja, Jc))
        cur = to_wag(*st[:5])
        r = transient(M, st, 10**11)
        if r[0] != 'OK':
            print('transient', r[0])
            return
        res = astep(*cur)
        if res[0] is None or (list(res[1]), res[2], list(res[3])) != to_wag(*r[1][:5]):
            bad += 1
            print('MISMATCH at transient', e, res[0])
        cnt[res[0]] += 1
        if res[0] and res[0].startswith('anom') and len(cur[0]) <= 2:
            B = (sum(cur[0]) + len(cur[0]) - 1 - 2) // 2
            margins.append((B - cur[1], B, cur[1], st[1]))
        st = r[1]
    print(dict(cnt), 'mismatches:', bad)
    big = [m for m in margins if m[1] >= 7]
    print('anomalies:', len(margins), ' smallest B - a:', min(margins), ' smallest B - a among B >= 7:', min(big),
          ' largest a:', max(m[2] for m in margins), ' largest k - B:', max(m[3] - m[1] for m in margins))


if __name__ == "__main__":
    main(int(sys.argv[1]))
