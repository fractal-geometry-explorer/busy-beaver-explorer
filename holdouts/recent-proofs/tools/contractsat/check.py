#!/usr/bin/env python3
"""Independent checker for a contractsat certificate (shares no code with the encoder).
usage: check.py cert.json   -> prints OK or raises."""
import sys, json
def check(cert):
    m = cert['machine']; mirror = cert['side'] == 'R'; n = cert['n']; W = cert['W']; phi = cert['phi']
    t = {}
    for i, p in enumerate(m.split('_')):
        for b in (0, 1):
            x = p[3*b:3*b+3]
            t[(i, b)] = None if x[0] == '-' else (int(x[0]), (x[1] == 'R') != mirror, ord(x[2]) - 65)
    S = len(m.split('_'))
    assert phi[0][0] == 0
    R = set(map(tuple, cert['R'])); T = set(map(tuple, cert['T'])); C = set(map(tuple, cert['C']))
    CC = set(map(tuple, cert['CC']))
    Rby = {}
    for (q, s, s2, q2) in R: Rby.setdefault((q, s), []).append((s2, q2))
    Tby = {}
    for (c, q, s, s2, p) in T: Tby.setdefault((c, q, s), []).append((s2, p))
    for c in (0, 1):
        for q in range(n):
            p = phi[c][q]
            for s in range(S):
                for (s2, p2) in Tby.get((c, q, s), []):
                    assert (p, s, s2, p2) in R, 'R not closed'
                if (p, s) in CC: assert (c, q, s) in C, 'C not closed'
                tr = t[(s, c)]
                if tr is None:
                    assert (c, q, s) not in C, 'halt inside a reachable call'
                    continue
                w, right, s3 = tr
                if not right:
                    assert (c, q, s, s3, phi[w][q]) in T, 'T: left move'
                else:
                    if (c, q, s) in C: assert (q, s3) in CC
                    for (s4, q2) in Rby.get((q, s3), []):
                        if (c, q, s) in C: assert (w, q2, s4) in C
                        for (s2, p2) in Tby.get((w, q2, s4), []):
                            assert (c, q, s, s2, p2) in T, 'T: right move'
    # window graph
    win = set((tuple(map(int, w)), pos, s, q) for (w, pos, s, q) in cert['window'])
    assert ((0,) * W, 0, 0, 0) in win
    for (word, pos, s, q) in win:
        word = list(word); seen = set()
        while True:
            key = (tuple(word), pos, s)
            if key in seen: break
            seen.add(key)
            tr = t[(s, word[pos])]
            assert tr is not None, 'halt in the window'
            w, right, s = tr
            word[pos] = w
            pos += 1 if right else -1
            if pos < 0:
                assert ((0,) + tuple(word[:-1]), 0, s, phi[word[-1]][q]) in win; break
            if pos >= W:
                assert (q, s) in CC
                for (s4, q2) in Rby.get((q, s), []):
                    assert (tuple(word), W - 1, s4, q2) in win
                break
    return True
if __name__ == '__main__':
    for f in sys.argv[1:]:
        check(json.load(open(f))); print('OK', f)
