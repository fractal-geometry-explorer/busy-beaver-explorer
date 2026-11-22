"""Era changes of the two-word sweeper 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB--- and its family: build an event tape by hand, run it to the next full events.

  python3 era_sweep.py demo     an era change of the run, and how an era change depends on N's lowest digits
  python3 era_sweep.py sweep    every era change with Z of 2 to 4 digits, X of 0 to 3 digits (every value), C of 5 digits
                                that wraps, R of 6 digits that overflows, N from 81 to 107: follows 12 events and reports
                                any halt

An event tape is 0^inf 1 0 [N] A> 0 [Z] 1 1 (0 1 1 0 [X] 1 1) [C] 0 1 [R] 0^inf with the digits of the README.
"""
import collections
import re

import sys
def parse(m):
    t={}
    for i,s in enumerate(m.split('_')):
        for r in range(2):
            x=s[3*r:3*r+3]
            if x[2]!='-': t[(i,r)]=(int(x[0]),1 if x[1]=='R' else -1,ord(x[2])-65)
    return t
class TM:
    def __init__(s,m,size=1<<20):
        s.tr=parse(m); s.t=bytearray(size); s.p=size//2; s.o=size//2; s.st=0; s.n=0; s.lo=s.hi=s.p
    def step(s):
        k=(s.st,s.t[s.p])
        if k not in s.tr: return False
        w,d,q=s.tr[k]; s.t[s.p]=w; s.p+=d; s.st=q; s.n+=1
        if s.p<s.lo: s.lo=s.p
        if s.p>s.hi: s.hi=s.p
        return True

M = '1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---'
D3 = {0: '100', 1: '110', 2: '010'}
T = {'00': 'z', '10': 'a', '01': 'c', '11': 'd'}
D3r = {'100': 0, '110': 1, '010': 2}
def build(N, nw, Zb, Xb, Cb, Rb, m=M):
    nd = [(N // 3**i) % 3 for i in range(nw)][::-1]   # most significant first
    left = '10' + ''.join(D3[d] for d in nd)
    right = '0' + ''.join('1010' if b else '0010' for b in Zb) + '11'
    if Xb is not None:
        right += '0110' + ''.join('1010' if b else '0010' for b in Xb) + '11'
    right += ''.join('0101' if b else '0001' for b in Cb) + '01' + ''.join('1010' if b else '1000' for b in Rb)
    tm = TM(m, 1 << 16); p0 = tm.p
    for i, ch in enumerate(left): tm.t[p0 - len(left) + i] = int(ch)
    for i, ch in enumerate(right): tm.t[p0 + i] = int(ch)
    tm.lo = p0 - len(left); tm.hi = p0 + len(right)
    return tm
def tape(tm):
    return ''.join(str(tm.t[i]) for i in range(tm.lo, tm.hi + 1))
def parse_at(tm):
    L = ''.join(str(tm.t[i]) for i in range(tm.lo, tm.p)); R = ''.join(str(tm.t[i]) for i in range(tm.p + 1, tm.hi + 1))
    n = nw = 0; pw = 1; l = L
    while len(l) >= 3 and l[-3:] in D3r: n += D3r[l[-3:]] * pw; pw *= 3; nw += 1; l = l[:-3]
    if l.lstrip('0') != '10': return None
    if len(R) < 4 or R[:4] not in ('0010', '1010'): return None
    s = R + '0000'; t = ''.join(T[s[i:i + 2]] for i in range(0, len(s) - 2, 2)).rstrip('z')
    return (n, nw, t)
def next_event(tm, maxsteps=10**6):
    k = 0
    while k < maxsteps:
        if not tm.step(): return ('HALT', k)
        k += 1
        if tm.st == 0 and tm.t[tm.p] == 0:
            r = parse_at(tm)
            if r: return (k, tm.p - (tm.o), r)
    return None
def words(t):
    m = re.match(r'^((?:za|aa)+)d(?:ca((?:za|aa)*)d)?((?:zc|cc)+)c((?:az|aa)+)$', t)
    if not m: return t
    z, x, c, r = m.groups(); x = x or ''
    b = lambda s, one: ''.join('1' if s[i:i+2] == one else '0' for i in range(0, len(s), 2))
    return 'Z=%s X=%s C=%s R=%s' % (b(z, 'aa'), b(x, 'aa'), b(c, 'cc'), b(r, 'aa'))

def demo():
    R = [(65533 >> i) & 1 for i in range(16)]
    tm = build(1017017, 14, [1] * 5, [1, 1, 0], [1] * 5, R)
    r = next_event(tm); print('the era change of step 173,165,846:', r[0], 'steps, N', r[2][0], 'Z X C R:', words(r[2][2]))
    print('k = 3, X = 0, Z = 111, C = 11101, R = 01111111; N from 999 to 1008:')
    for N in range(999, 1009):
        tm = build(N, 7, [1] * 3, [0, 0, 0], [1, 0, 1, 1, 1], [0] + [1] * 7)
        r = next_event(tm, 200000); print('  N', N, '(N mod 9 =', N % 9, ') ->', r[0], 'steps, event at cell', r[1], 'N', r[2][0], '(%d digits)' % r[2][1], words(r[2][2]))

def sweep():
    cnt = collections.Counter(); halts = []
    for k in (0, 1, 2, 3):
      for zw in (2, 3, 4):
        for xv in range(1 << k):
          a = 3 if k == 0 else (24 >> k) + (3 if xv == (1 << k) - 1 else 0)
          for cw in (5,):
            for cv in range(max(0, (1 << cw) - a), 1 << cw):
              for rw in (6,):
                for rv in range((1 << rw) - 3, 1 << rw):
                  for N in range(81, 81 + 27):
                    tm = build(N, 5, [1] * zw, None if k == 0 else [(xv >> i) & 1 for i in range(k)], [(cv >> i) & 1 for i in range(cw)], [(rv >> i) & 1 for i in range(rw)])
                    # follow up to 30 events
                    res = 'ok'
                    for e in range(12):
                        r = next_event(tm, 300000)
                        if r is None: res = 'long'; break
                        if r[0] == 'HALT': res = 'HALT'; halts.append((k, zw, xv, cw, cv, rw, rv, N, e)); break
                    cnt[res] += 1
    print(dict(cnt)); print(halts[:20])


if __name__ == "__main__":
    demo() if sys.argv[1:] == ["demo"] else sweep()
