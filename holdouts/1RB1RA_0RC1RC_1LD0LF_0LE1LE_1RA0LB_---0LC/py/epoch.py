"""Run one epoch (exactly, with the divide-and-conquer parity iteration of fastwalk.py; gmpy2 if installed)
of of 1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC's macro machine exactly.

Macro state X(n, m) = C>0 0^n 1^m 0 1 (n even, j = n/2, y = j + 4).  For m >= 2: y -> ceil(3y/2) and m -= 1 (y even)
or 2 (y odd).  m = 1: y even -> (y', 0) with the same map; y odd -> reset X(4, 3j + 6).  m = 0: y even -> reset
X(4, 3j + 5); y odd -> halt.
"""
import sys, time
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import fastwalk as fw
from fastwalk import run, mpz, popcount, bit

def epoch(m, y=6, C=1 << 20, verbose=True):
    """Returns ('halt', t) or ('reset', t, new_m); t = macro steps in this epoch."""
    t = 0
    t0 = time.time()
    while True:
        mask = (mpz(1) << C) - 1
        l, h = y & mask, y >> C
        g, bits = run(l, C)
        dec = C + popcount(bits)
        if m - dec >= 2:
            m -= dec; t += C
            y = fw.p3(C) * h + g
            if verbose and (t // C) % 16 == 0:
                print(f't={t} m={m} bits(y)={y.bit_length()} {time.time()-t0:.0f}s', flush=True)
            continue
        # the end is in this chunk: walk its parities
        bstr = format(int(bits), 'b').zfill(C)[::-1]
        for s in range(C):
            odd = bstr[s] == '1'
            if m >= 2:
                m -= 2 if odd else 1
                continue
            # m in {0, 1} at macro step s of the chunk: need exact y_s
            gs, _ = run(l, s)
            ys = (fw.p3(s) * h << (C - s)) + gs
            j = ys - 4
            if m == 1:
                if odd: print('end: m = 1, n = 2 mod 4'); return ('reset', t + s + 1, 3 * j + 6, ys)
                m = 0
                continue
            if odd: return ('halt', t + s + 1, ys)
            print('end: m = 0, n = 0 mod 4'); return ('reset', t + s + 1, 3 * j + 5, ys)
        # chunk ended exactly with m in {0,1} pending (m decremented but no end yet): advance and continue
        t += C
        y = fw.p3(C) * h + g

# usage: python3 py/epoch.py M [LOG2_CHUNK]   e.g. 57 -> reset with m = 210273201; 210273201 22 -> reset (35 s with gmpy2)
if __name__ == '__main__':
    m = int(sys.argv[1]); C = 1 << int(sys.argv[2]) if len(sys.argv) > 2 else 1 << 20
    r = epoch(m, C=C)
    print(r[0], r[1], (r[2] if r[2] < 10**30 else f'{r[2].bit_length()} bits') if r[0]=='reset' else '')
    if r[0] == 'reset':
        mm = r[2]
        print('new m mod 2^64 =', int(mm & ((1 << 64) - 1)), ' decimal digits =', len(str(int(mm))) if mm < (1 << 300000) else 'about %d' % int(mm.bit_length() * 0.30103))
