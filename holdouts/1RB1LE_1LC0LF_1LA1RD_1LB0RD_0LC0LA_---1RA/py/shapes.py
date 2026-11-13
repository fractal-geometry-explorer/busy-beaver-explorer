"""shapes.py M STEPS [EVERY]: at head turns, tokenize the tape into maximal powers u^k of short words (|u| <= 4,
greedy, left to right) and report, per decade of steps, the largest number of tokens seen and the number of
distinct token shapes (exponents >= 3 replaced by '*').  A frame map with finitely many frames and scalar
parameters needs both to stay bounded."""
import sys
def parse_m(m):
    t = {}
    for i, g in enumerate(m.split('_')):
        for b in (0, 1):
            w = g[3*b:3*b+3]; t[(i, b)] = None if w[0] == '-' else (int(w[0]), 1 if w[1] == 'R' else -1, ord(w[2]) - 65)
    return t
def tokens(s):
    out = []; i = 0; n = len(s)
    while i < n:
        best = (1, 1)  # (coverage, len u)
        for L in range(1, 5):
            u = s[i:i+L]
            if len(u) < L: break
            k = 1
            while s[i+k*L:i+(k+1)*L] == u: k += 1
            if k * L > best[0] * best[1] or (k > 1 and k * L > best[0]):
                if k * L > best[0] * (1 if best[1] == 1 and best[0] == 1 else 1): best = (k * L, L) if k > 1 else best
        cov, L = best
        if cov > L:
            k = cov // L; out.append((s[i:i+L], k)); i += k * L
        else:
            out.append((s[i], 1)); i += 1
    # merge consecutive single chars into one literal token
    m = []
    for u, k in out:
        if k == 1 and m and m[-1][1] == 1 and len(m[-1][0]) < 4: m[-1] = (m[-1][0] + u, 1)
        else: m.append((u, k))
    return m
def main(M, N, every):
    T = parse_m(M); tape = bytearray(200000); p = 100000; st = 0; lo = hi = p; prevd = 0; turns = 0
    dec = 10000; mx = 0; shapes = set(); allshapes = set()
    for n in range(1, N + 1):
        tr = T[(st, tape[p])]
        if tr is None: print('halt', n); return
        tape[p] = tr[0]; d = tr[1]; p += d; st = tr[2]; lo = min(lo, p); hi = max(hi, p)
        if d != prevd:
            turns += 1
            if turns % every == 0:
                s = ''.join('01'[x] for x in tape[lo:p]) + 'ABCDEF'[st] + ''.join('01'[x] for x in tape[p:hi + 1])
                s = s.strip('0') if True else s
                tk = tokens(s)
                mx = max(mx, len(tk)); sh = tuple((u, k if k < 3 else '*') for u, k in tk); shapes.add(sh); allshapes.add(sh)
        prevd = d
        if n == dec:
            print(f"steps <= {n:>12,}: max tokens {mx:3d}, new shapes in decade {len(shapes):6d}, total {len(allshapes)}", flush=True)
            shapes = set(); dec *= 10
if __name__ == '__main__':
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 1)
