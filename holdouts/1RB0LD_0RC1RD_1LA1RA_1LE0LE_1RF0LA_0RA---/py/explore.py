"""Check the P-map of 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA--- by direct simulation.
P(n) = (101)^n 01 A> 0.   python3 explore.py pmap 150"""
import sys
from sim import next_event, expand
N = int(sys.argv[2]) if len(sys.argv) > 2 else 150
bad = 0
for n in range(1, N):
    got = next_event('(101)^%d 01 A> 0' % n, 'A', 'R')
    k, e = divmod(n, 3)
    m = [4 * k + 2, 4 * k + 3, 4 * k + 4][e]
    word = ['01', '01', '10'][e]
    exp = ('(101)^%d %s A> 0' % (m, word), [27*k*k + 87*k + 35, 27*k*k + 105*k + 62, 27*k*k + 123*k + 103][e])
    if expand(got[0]) != expand(exp[0]) or got[1] != exp[1]:
        bad += 1; print('differs', n, got, exp)
print('P-map checked for 1 <= n <', N, ':', 'all agree' if not bad else '%d differ' % bad)
