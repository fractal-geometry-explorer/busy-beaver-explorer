#!/usr/bin/env python3
"""The block of 1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC as a device of its own (README "The odometer").

The block is a row of 4-cell words followed by blank tape: 0110 = digit 0, 0010 = digit 1, 1110 = digit 2,
0000 = h (a half-finished digit; also the blank).  A *send* is the head entering the first cell of the block from
the left in state A or E and coming back out on the left (in state B or D in the real run).

  python3 py/block.py rules        # the send rules on small blocks (direct simulation)
  python3 py/block.py explore K ML # all blocks reachable from K zero digits by free A/E sends, words <= ML
  python3 py/block.py halt         # shortest free sequence of sends from all-zero blocks that halts or returns in
                                   # a state other than B, D: the block is NOT safe under free interleaving
"""
import sys
from collections import deque, Counter
MS = "1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC"
T = {}
for si, row in enumerate(MS.split('_')):
    for b in (0, 1):
        x = row[3*b:3*b+3]
        T[(si, b)] = None if x[0] == '-' else (int(x[0]), 1 if x[1] == 'R' else -1, ord(x[2]) - 65)
Z = (0, 1, 1, 0)
NAME = {(0, 1, 1, 0): '0', (0, 0, 1, 0): '1', (1, 1, 1, 0): '2', (0, 0, 0, 0): 'h'}


def send(words, st, cap=200000):
    """words: list of 4-tuples, then blank; the head enters cell 0 in state st.  Returns (state, words) when the
    head leaves on the left, ('HALT', None) or ('LOOP', None)."""
    c = [b for w in words for b in w] + [0] * 24
    p = 0
    k = 0
    while p >= 0:
        if p >= len(c) - 8:
            c += [0] * 16
        r = T[(st, c[p])]
        if r is None:
            return ('HALT', None)
        c[p] = r[0]
        p += r[1]
        st = r[2]
        k += 1
        if k > cap:
            return ('LOOP', None)
    ws = [tuple(c[i:i+4]) for i in range(0, len(c) - len(c) % 4, 4)]
    while ws and ws[-1] == (0, 0, 0, 0):
        ws.pop()
    return (st, tuple(ws))


def fmt(s):
    return " ".join(NAME.get(w, "".join(map(str, w))) for w in s) or "(empty)"


def explore(K, maxlen, limit=200000):
    start = tuple([Z] * K)
    seen = {start}
    q = deque([start])
    rets = Counter()
    bad = []
    while q and len(seen) < limit:
        s = q.popleft()
        for st in (4, 0):
            r, ns = send(list(s), st)
            if r in ('HALT', 'LOOP'):
                bad.append((s, st, r))
                continue
            rets["ABCDEF"[st] + "->" + "ABCDEF"[r]] += 1
            if r not in (1, 3):
                bad.append((s, st, "returns " + "ABCDEF"[r]))
                continue
            if len(ns) > maxlen:
                continue
            if ns not in seen:
                seen.add(ns)
                q.append(ns)
    return seen, rets, bad


def path(K, ML):
    start = tuple([Z] * K)
    par = {start: None}
    q = deque([start])
    while q:
        s = q.popleft()
        for st in (4, 0):
            r, ns = send(list(s), st)
            if r == 'HALT' or (r != 'LOOP' and r not in (1, 3)):
                out = [(s, st, r)]
                x = s
                while par[x] is not None:
                    out.append(par[x] + ('',))
                    x = par[x][0]
                return out[::-1]
            if r == 'LOOP' or len(ns) > ML:
                continue
            if ns not in par:
                par[ns] = (s, st)
                q.append(ns)


def val(s):
    D = {'0': 0, '1': 1, '2': 2}
    return [NAME.get(w, '?') for w in s]


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "rules"
    if cmd == "rules":
        d = {'0': Z, '1': (0, 0, 1, 0), '2': (1, 1, 1, 0), 'h': (0, 0, 0, 0)}
        for src in ["000", "100", "010", "200", "210", "220", "h00", "0h0", "120", "012", "021", "0021"]:
            for st in (0, 4):
                r, ns = send([d[ch] for ch in src], st)
                print(f"{'AE'[st == 4]}-send on {' '.join(src)} (lowest digit first): returns "
                      f"{r if isinstance(r, str) else 'ABCDEF'[r]}, block {fmt(ns) if ns is not None else '-'}")
    elif cmd == "explore":
        K, ML = int(sys.argv[2]), int(sys.argv[3])
        seen, rets, bad = explore(K, ML)
        print("blocks", len(seen), "returns", dict(rets), "bad", len(bad))
        for s, st, r in bad[:15]:
            print("  ", fmt(s), ": send", "ABCDEF"[st], r)
    elif cmd == "halt":
        for K in (1, 2, 3, 4):
            p = path(K, K + 3)
            print("start with", K, "zero digits:", len(p) - 1, "sends, then")
            for s, st, r in p:
                print("   ", fmt(s), ": send", "ABCDEF"[st],
                      ("-> " + (r if r == 'HALT' else "returns " + "ABCDEF"[r])) if r != '' else '')
