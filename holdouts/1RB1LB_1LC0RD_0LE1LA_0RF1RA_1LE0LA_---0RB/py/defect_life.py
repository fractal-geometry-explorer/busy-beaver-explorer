"""The life of a bulk `10` defect of 1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB, sweep by sweep, against the jump model.

Input: the output of c/turns.c (`./turns 12000000 150 > turns.txt`): the tape tokenized at every left turn.  Keeps the
tapes with exactly one bulk `T` (more than 30 tokens from the right end) whose 10 words before it hold no wall, and one
line per change of (10 words before T, gap up to the next wall): each change is one deep sweep.  Checks:

  rules  each deep sweep is `shielded` (x before T) or `jump` (y before T) of lean/Hop.lean, on the 10 words before T
         and on the gap words the old gap determines; a jump whose first x block runs into the wall is a merge (T and
         wall cancel, the lifetime ends);
  series the gap, read with T as the constant term, W = 1 + g0 z + g1 z^2 + ..., is multiplied by 1 + z every shielded
         sweep, and a jump W = (1 + z + ... + z^j) + z^L C (L = j + a + 2) gives (1 + z) C;
  clock  after a jump over m = j + a + 1 slots the next jump comes exactly m sweeps later (the words before T are then
         x^m y, so the Lucas sum of the left words is first y at sweep m).

usage: python3 defect_life.py turns.txt
"""
import sys

K = 10


def x102(ws, q):
    v = [w == 'y' for w in ws] + [q == 'y']
    return ''.join('y' if v[i] != v[i + 1] else 'x' for i in range(len(ws)))


def deep_sweeps(path):
    rows, prev = [], None
    for ln in open(path):
        f = ln.split()
        if f[0] == 'HALT':
            raise SystemExit('halted')
        s = f[2]
        ts = [i for i, c in enumerate(s) if c == 'T' and len(s) - i > 30 and i > K + 2]
        if len(ts) != 1 or 'o' in s[ts[0] - K:ts[0]]:
            if prev is not None:
                rows.append(None)
            prev = None
            continue
        i = ts[0]
        j = i + 1
        while j < len(s) and s[j] in 'xy':
            j += 1
        cur = (int(f[0]), s[i - K:i], s[i + 1:j])
        if prev is None or prev[1:] != cur[1:]:
            rows.append(cur)
        prev = cur
    return rows


def main(path):
    rows = deep_sweeps(path)
    n = {'shielded': 0, 'jump': 0, 'merge': 0}
    bad, clock_ok, clock_n, series_ok, series_n, since = 0, 0, 0, 0, 0, None
    jumps = []
    for r0, r1 in zip(rows, rows[1:]):
        if r0 is None:
            since = None
            continue
        k, P, G = r0
        if P[-1] == 'x':
            kind = 'shielded'
            wantP, wantG = x102(P[:-1], 'x')[1:], x102('y' + G, 'x')[:max(0, len(G) - 1)]
            W = [1] + [c == 'y' for c in G]
            nextW = [W[0]] + [W[i] ^ W[i - 1] for i in range(1, len(W))]
        else:
            j = 0
            while j < len(G) and G[j] == 'y':
                j += 1
            a = 0
            while j + a < len(G) and G[j + a] == 'x':
                a += 1
            if j == len(G):
                raise SystemExit(f'danger pattern at step {k}')
            C = G[j + a:]
            kind = 'jump' if C else 'merge'
            m = j + a
            jumps.append((k, j, a, len(G)))
            wantP = (x102(P, 'x') + 'x' * m)[-(K - 1):]
            wantG = x102(C, 'x')[:max(0, len(C) - 1)]
            Cb = [c == 'y' for c in C]
            nextW = [1] + [Cb[i] ^ Cb[i + 1] for i in range(len(Cb) - 1)]
        n[kind] += 1
        if kind != 'shielded' and since is not None:
            clock_n += 1
            clock_ok += since == 0
        if kind == 'merge' or r1 is None:
            since = None
        elif kind == 'jump':
            since = m
        elif since is not None:
            since -= 1
        if kind == 'merge' or r1 is None:
            continue
        _, P1, G1 = r1
        ok = P1.endswith(wantP[-(K - 3):]) and G1.startswith(wantG)
        bad += not ok
        W1 = [1] + [c == 'y' for c in G1]
        m2 = min(len(W1), len(nextW))
        series_n += 1
        series_ok += W1[:m2] == nextW[:m2]
    print(f"deep sweeps: {n['shielded']} shielded, {n['jump']} jumps, {n['merge']} merges; rule mismatches: {bad}")
    print(f"series: {series_ok} of {series_n} gaps agree with the 1 + z model on the words the old gap determines")
    print(f"clock: {clock_ok} of {clock_n} jumps and merges after a first jump came exactly m sweeps after the previous jump")
    print("jumps and merges (step, j, a+1, gap length):", ' '.join(f"({k},{j},{a},{g})" for k, j, a, g in jumps))


if __name__ == '__main__':
    main(sys.argv[1])
