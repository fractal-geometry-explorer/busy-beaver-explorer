"""The pass machine of lean/Sweep.lean, transcribed: mstep(out, rest) -> ('go', n, out', rest') or ('halt', n).

Lists of bools; `out` is the list of pairs left of the head, nearest first (True = 11, False = 01).
Run as a script: python3 passmachine.py N  checks the first N macro steps against a direct simulation."""
import sys

EDGE = "34"   # which left-edge rules (set by the 35 copy)


def cells(q):
    out = []
    for b in q:
        out += [b, True]
    return out


def scanF(l, m):
    """Lean's scanF: returns (kind, n, data).  l nearest first; m in reading order (head first)."""
    n = 0
    i = 0
    acc = []          # pairs passed, nearest last (so reading order is reversed(acc) + m)
    L = len(l)
    def mm(extra=()):
        return list(reversed(acc)) + list(extra) + list(m) if False else list(extra) + list(reversed(acc)) + list(m)
    while True:
        if i >= L:
            return ('edgeD', n, list(reversed(acc)) + list(m))
        if l[i]:
            acc.append(True); n += 2; i += 1; continue
        if i + 1 >= L:
            acc.append(False)
            return ('edgeE', n + 2, list(reversed(acc)) + list(m))
        if l[i + 1]:
            acc.append(False); acc.append(False); n += 4; i += 2; continue
        if i + 2 >= L:
            return ('halt', n + 4, None)
        acc.append(False); acc.append(True); acc.append(l[i + 2])
        return ('turn', n + 5, (l[i + 3:], list(reversed(acc)) + list(m)))


def apass(cs, cl):
    """Lean's apass. cs: left pairs nearest first; cl: cells."""
    st = list(reversed(cs))   # nearest last
    n = 0
    i = 0
    L = len(cl)
    while True:
        a = cl[i] if i < L else False
        b = cl[i + 1] if i + 1 < L else False
        if b:
            st.append(not a); n += 2; i += 2; continue
        if a:
            if not st:
                return ('halt', n + 3)
            st[-1] = not st[-1]; st.append(False); n += 8; i += 2; continue
        return ('go', n + 2, list(reversed(st)), list(cl[i + 2:]))


def mstep(out, rest):
    k, n, d = scanF(out, [False])
    if k == 'turn':
        cs, q = d
        r = apass(cs, cells(q) + rest)
        n += 1
    elif k == 'edgeD':
        r = apass([True], [False] + cells(d) + rest) if EDGE == "34" else edge35D(d, rest)
        n += 5
    elif k == 'edgeE':
        r = apass([True], cells(d) + rest) if EDGE == "34" else edge35E(d, rest)
        n += 4
    else:
        return ('halt', n + 1)
    if r[0] == 'halt':
        return ('halt', r[1] + n)
    return ('go', r[1] + n, r[2], r[3])


def word(out):
    """the word (reading order) of a turn configuration with rest = []: out reversed, then the pair under the head."""
    return [b for b in reversed(out)] + [True]
