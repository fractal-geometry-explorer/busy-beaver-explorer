"""The words around a bulk `10` defect of 1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB, in the defect's frame.

Input: the output of c/defect10.c (`./defect10 9000000 1 > d10.txt`).  Keeps the 10s more than 30 tokens from the
right end with a `0` wall after the gap, and one line per change of (last 12 words before the 10, gap).  Checks, with
words indexed left to right and the 10 kept in place:

  left: the words before the 10 go from l to l' with l'[i] = l[i-1] xor l[i]     (count updates with no wall within 12)
  gap:  the gap words go from g to g' with g'[j] = g[j-1] xor g[j], g[-1] = y      (count updates of unchanged length)
  Lucas: so the word just before the 10, t updates after the first sighting, is the XOR of the words
         L_(1+k) (k-th word left of it at the start) over the k whose binary digits lie inside those of t.

usage: python3 defect_frame.py d10.txt
"""
import re
import sys

v = {'x': 0, 'y': 1}


def main(path):
    rows = []
    for ln in open(path):
        f = ln.split()
        if not f or f[0] != 'G' or int(f[3]) <= 30:
            continue
        step, left = int(f[1]), f[5]
        gap, after = (f[6], f[7]) if len(f) == 8 else ('', f[6])
        if after != '3':
            continue
        key = (left[-12:], gap)
        if rows and rows[-1][3] == key:
            continue
        rows.append((step, left, gap, key))
    segs, cur = [], []
    for r in rows:
        if cur and r[0] - cur[-1][0] > 400000:
            segs.append(cur)
            cur = []
        cur.append(r)
    segs.append(cur)
    lokx = lok = lbad = gok = gbad = pok = pbad = 0
    for sg in segs:
        for a, b in zip(sg, sg[1:]):
            la, lb = a[1][-12:], b[1][-12:]
            if re.fullmatch('[xy]+', la) and re.fullmatch('[xy]+', lb):
                if all(v[lb[i]] == v[la[i - 1]] ^ v[la[i]] for i in range(1, 12)):
                    lok += 1
                    lokx += la[-1] == 'x'
                else:
                    lbad += 1
                    print("left update not of that form: steps %d -> %d, %s -> %s" % (a[0], b[0], la, lb))
            if len(a[2]) == len(b[2]) and a[2] != b[2]:
                w = [1] + [int(c) for c in a[2]]
                if ''.join(str(w[j - 1] ^ w[j]) for j in range(1, len(w))) == b[2]:
                    gok += 1
                else:
                    gbad += 1
        m = re.search('[xy]+$', sg[0][1])
        L = [v[c] for c in m.group(0)][::-1]
        for t, r in enumerate(sg):
            if t >= len(L):
                break
            pred = 0
            for k in range(t + 1):
                if k & t == k:
                    pred ^= L[k]
            if r[1][-1] in 'xy':
                if pred == v[r[1][-1]]:
                    pok += 1
                else:
                    pbad += 1
                    print("Lucas prediction first fails at step %d (t = %d), lifetime starting %d" % (r[0], t, sg[0][0]))
                    break
    print("left updates: %d follow l'[i] = l[i-1] xor l[i] (%d of them with x before the 10), %d do not" % (lok, lokx, lbad))
    print("gap updates:  %d follow g'[j] = g[j-1] xor g[j] with y before, %d do not" % (gok, gbad))
    print("word before the 10 predicted by Lucas up to the first failure: %d" % pok)


if __name__ == '__main__':
    main(sys.argv[1])
