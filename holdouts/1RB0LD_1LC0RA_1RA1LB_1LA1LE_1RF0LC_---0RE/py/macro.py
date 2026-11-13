"""The macro step of 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE, three ways:

* `pstep(n)`: a transcription of `pstep` in lean/Macro.lean (doubling rounds, then the end of the phase), with its
  exact step count;
* `closed(n)`: the closed form  n' = 3n - 10*2^k + 3k + 14  for h_k < n < h_{k+1},  h_k = 5*2^k - k - 6, which halts
  exactly at n = h_k, with steps 12 r^2 + (40*2^k + 6) r + (100*4^k + 23)/3 - 10*2^k,  r = n - h_k - 1;
* `python3 macro.py check N`: the two agree for 1 <= n <= N (and with a direct simulation for small n, see
  `simulate.py`).
"""
import sys


def zsteps(b, j):
    # sum_{i<j} 4(b+2i)+8
    return j * (4 * b + 8) + 4 * j * (j - 1)


def xsteps(c, j):
    # sum_{i<j} 4(c+2i)+10
    return j * (4 * c + 10) + 4 * j * (j - 1)


def tend(c, m):
    if m == 0:
        return ('halt', 2 * c)
    if m == 1:
        return ('halt', 2 * c + 2)
    if m == 2:
        return ('go', c + 3, (2 * (c - 1) + 8) + xsteps(c, 1) + 1)
    j, e = divmod(m - 3, 2)
    if j < c:
        if e == 0:
            return ('go', c + 3 * j + 5, (2 * c + 3) + zsteps(0, j) + (8 * j + 7) + xsteps(c - j, 2 * j + 2) + 1)
        return ('go', c + 3 * j + 6,
                (2 * c + 3) + zsteps(0, j) + (16 * j + 4 * (c - j - 1) + 29) + xsteps(c - j + 1, 2 * j + 2) + 1)
    r = m - 3 - 2 * c
    if r == 0:
        return ('go', 4 * c + 5, (2 * c + 3) + zsteps(0, c) + (8 * c + 7) + xsteps(0, 2 * c + 2) + 1)
    if r == 1:
        return ('go', 4 * c + 6, (2 * c + 3) + zsteps(0, c) + (16 * c + 25) + xsteps(1, 2 * c + 2) + 1)
    return ('go', 4 * c + 8, (2 * c + 3) + zsteps(0, c) + (16 * c + 65) + xsteps(5, 2 * c + 1) + 1)


def tphase(c, m):
    t = 0
    while 2 * c + 6 <= m:
        t += (2 * c + 3) + zsteps(0, c) + (16 * c + 23)
        m -= 2 * c + 6
        c = 2 * c + 4
    o = tend(c, m)
    return o[:-1] + (o[-1] + t,)


def pstep(n):
    o = tphase(1, 2 * n + 2)
    return o[:-1] + (o[-1] + 2 * n + 8,)


def h(k):
    return 5 * 2 ** k - k - 6


def closed(n):
    k = max(0, n.bit_length() - 4)
    while k > 0 and h(k) >= n:
        k -= 1
    while h(k + 1) < n:
        k += 1
    if h(k + 1) == n or (k > 0 and h(k) == n):
        return ('halt',)
    r = n - h(k) - 1
    return ('go', 5 * 2 ** k - 1 + 3 * r, 12 * r * r + (40 * 2 ** k + 6) * r + (100 * 4 ** k + 23) // 3 - 10 * 2 ** k)


if __name__ == '__main__':
    if sys.argv[1:2] == ['check']:
        N = int(sys.argv[2])
        for n in range(1, N + 1):
            a, b = pstep(n), closed(n)
            if a[0] == 'halt':
                assert b[0] == 'halt', (n, a, b)
            else:
                assert a == b, (n, a, b)
        print('pstep == closed form for 1 <= n <=', N)
    elif sys.argv[1:2] == ['orbit']:
        # P-events from blank tape (P(4) at step 31) up to a step bound: compare with c/pevents.c
        bound, n, t = int(float(sys.argv[2])), 4, 31
        while t <= bound:
            print(t, n)
            o = closed(n)
            if o[0] == 'halt':
                print('HALT at P', n)
                break
            n, t = o[1], t + o[2]
    elif sys.argv[1:2] == ['far']:
        # iterate the closed form K macro steps from P(4); report the size of n and of the step count
        K, n, t = int(float(sys.argv[2])), 4, 31
        for i in range(1, K + 1):
            o = closed(n)
            if o[0] == 'halt':
                print('HALT at macro step', i, 'n =', n)
                break
            n, t = o[1], t + o[2]
            if i % (K // 10 or 1) == 0:
                print(i, 'macro steps: n has', n.bit_length(), 'bits; steps ~ 10^%d' % int(t.bit_length() * 0.30103), flush=True)
