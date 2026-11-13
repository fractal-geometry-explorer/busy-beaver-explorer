"""The quadrupling round of 1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA--- (and of its relabelling
1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD---, whose state B is this machine's C):

    C> 000 (100)^c (010)^(b+2c+1) X   ->   C> 000 (100)^(4c) (010)^b X      in 60c^2 + 13c + 39 steps   (c >= 3)

(head at the left end of the tape; the next moment it is there again in state C reading 000).  Checked by direct
simulation for c = 3..39, b = 0..7 and several tails X.   python3 quadround.py [MACHINE STATE]"""
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
M = sys.argv[1] if len(sys.argv) > 1 else '1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA---'
S = sys.argv[2] if len(sys.argv) > 2 else 'C'
d = tempfile.mkdtemp()
exe = os.path.join(d, 'evrun2')
subprocess.check_call(['gcc', '-O2', '-o', exe, os.path.join(HERE, '..', '..', '1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---',
                                                              'c', 'evrun2.c')])
p = subprocess.Popen([exe, M, S, '000', '1000000000'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
n = bad = 0
for c in range(3, 40):
    for b in range(0, 8):
        for X in ['01', '0001001', '01101', '0100100100101']:
            p.stdin.write('000' + '100' * c + '010' * (b + 2 * c + 1) + X + '\n')
            f = p.stdout.readline().split()
            n += 1
            if len(f) < 2 or f[1] != ('000' + '100' * (4 * c) + '010' * b + X).rstrip('0') or \
                    int(f[0]) != 60 * c * c + 13 * c + 39:
                bad += 1
                print('differs', c, b, X, f[:1])
print('%s: quadrupling round checked in %d cases, %d differ' % (M, n, bad))
sys.exit(1 if bad else 0)
