"""Exact block model of 1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB.

P(n)          = 0^inf E> 0 0 1^n 0 1 0^inf                       (head at the left end)
E(S, p, q, r) = 0^inf 1^S1 0 0 ... 1^Sk 0 0 1^p 0 0 1^q 0 1^r E> 0^inf   (head at the right end)

P(n) -> E([], 2, n-2, 2) in 5n-6 steps, then one sweep at a time:
  q >= 4          : (p+2, q-2, r+1)                 8q + 4r - 9 steps
  q = 3           : (p+2, 1, r+1)                   4r + 15
  q = 2, r = 1    : (p+2, 3, 1)                     31
  q = 2, r = 2    : HALT                            21 (the last one is the halting transition)
  q = 2, r >= 3   : push p+2, (1, r-2, 1)           8r
  q = 1, S = S'.x : (S', x, p+r+4, 1)               8r + 22
  q = 1, S = []   : P(p+r+4)                        3p + 11r + 35
Once (q, r) = (2, 3) occurs the machine never halts: (p, 2, 3) -> push p+2, (1, 1, 1) -> pop (p+2, 6, 1) -> (p+6, 2, 3).

Usage:
  python3 model.py blank 1e10      P-events from blank tape up to a step bound (compare with c/pevents.c)
  python3 model.py far 650         follow the run for that many P-rounds
  python3 model.py frac 4000       halting / runaway fraction of the next round from random P(n), by size of n
"""
import sys, math, random
sys.set_int_max_str_digits(0)


def run_P(n, t=0, maxops=10**7, onP=None, maxP=None):
    """From P(n) at time t: ('halt', t_halt) / ('runaway', t) / ('limitP', t, n) / ('limit', ...)."""
    S = []; nP = 0
    p, q, r = 2, n - 2, 2; t += 5 * n - 6
    ops = 0
    while ops < maxops:
        ops += 1
        if q >= 4:
            j = (q - 2) // 2      # j sweeps at once
            t += j * (8 * q + 4 * r - 9) - 6 * j * (j - 1); p += 2 * j; r += j; q -= 2 * j
        elif q == 3:
            t += 4 * r + 15; p += 2; q = 1; r += 1
        elif q == 2:
            if r == 1: t += 31; p += 2; q = 3; r = 1
            elif r == 2: return ('halt', t + 21, S, p)
            else:
                t += 8 * r; S.append(p + 2); p, q, r = 1, r - 2, 1
        elif q == 1:
            v = p + r + 4
            if S:
                t += 8 * r + 22; p, q, r = S.pop(), v, 1
                if q == 6 and r == 1: return ('runaway', t, S, p)
            else:
                t += 3 * p + 11 * r + 35; nP += 1
                if onP: onP(v, t)
                if maxP and nP >= maxP: return ('limitP', t, v)
                n = v; t += 5 * n - 6; p, q, r = 2, n - 2, 2
        else:
            raise Exception('q=%d' % q)
    return ('limit', t, len(S), p, q, r)


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'blank'
    if cmd == 'blank':
        bound = int(float(sys.argv[2])); ev = [(51, 5)]
        def onP(v, t):
            if t > bound: raise StopIteration
            ev.append((t, v))
        try: run_P(5, 51, maxops=10**8, onP=onP)
        except StopIteration: pass
        for t, v in ev: print(t, v)
    elif cmd == 'far':
        K = int(float(sys.argv[2])); cnt = [0]
        def onP(v, t):
            cnt[0] += 1
            if cnt[0] % max(1, K // 20) == 0 or cnt[0] == K:
                print('P-round', cnt[0], 'n has %d bits, step ~ 10^%.1f' % (v.bit_length(), t.bit_length() * math.log10(2)), flush=True)
        res = run_P(5, 51, maxops=10**12, onP=onP, maxP=K)
        print('RESULT', res[0])
    elif cmd == 'frac':
        N = int(sys.argv[2]); random.seed(1)
        for d in [6, 8, 10, 12, 15, 20, 25, 30, 40]:
            c = {}
            for _ in range(N):
                n = random.randrange(10 ** (d - 1), 10 ** d)
                k = run_P(n, maxops=10**6, maxP=1)[0]
                c[k] = c.get(k, 0) + 1
            print(d, 'digits:', ', '.join('%s %d' % kv for kv in sorted(c.items())), 'of', N, flush=True)
