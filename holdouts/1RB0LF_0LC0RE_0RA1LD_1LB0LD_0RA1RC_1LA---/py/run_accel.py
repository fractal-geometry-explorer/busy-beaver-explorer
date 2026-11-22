"""Runs the block macro machine with record skipping (accel.py): this machine from record 1, or the twin
1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD--- from its record 6 (as py/twin.py).  Chunks of 2^J records, J growing with the
record count (J = max(J0, bits(records) - SLACK)); prints a line whenever the reset count changes or every PRINT
seconds.  A reset is a record 0^inf 1 B> 1 (0, o) (X, x) ... with X >= 36.
The memo is cleared whenever it holds more than LIMIT transforms (default 200,000).
At the end it prints a STATE line; giving that output file instead of own|twin resumes from it.
usage: python3 run_accel.py own|twin|FILE SECONDS [J0 SLACK PRINT LIMIT]"""
import sys, time
from accel import Acc, apply
which, secs = sys.argv[1], float(sys.argv[2])
J0 = int(sys.argv[3]) if len(sys.argv) > 3 else 20
SLACK = int(sys.argv[4]) if len(sys.argv) > 4 else 8
PRINT = float(sys.argv[5]) if len(sys.argv) > 5 else 60
LIMIT = int(float(sys.argv[6])) if len(sys.argv) > 6 else 200000
resets = 0
if which == 'own':
    st, steps, rec = ((), 0, [(0, 1), (1, 0)]), 4, 1
elif which == 'twin':
    st, steps, rec = ((), 0, [(3, 0), (0, 0), (1, 1), (1, 1), (1, 1), (1, 0)]), 157, 6
else:                     # resume from a STATE line saved in a file
    import ast
    line = [l for l in open(which) if l.startswith('STATE ')][-1]
    ell, c, bl, steps, rec, resets = ast.literal_eval(line[6:])
    st = (ell, c, bl)
A = Acc(); A.cleared = 0; t0 = time.time(); last = 0


def show(tag):
    bl = st[2]
    w = lambda D: ('%d' % D) if D < 10 ** 12 else ('%.6e' % D)
    print('%s rec %.6e steps %.6e (10^%d) resets %d blocks %d head %d%d %s time %.0f transforms %d' % (
        tag, rec, steps, len(str(steps)) - 1, resets, len(bl), len(st[0]), st[1],
        ' '.join(w(D) + 'oi'[x] for D, x in bl[:4]), time.time() - t0, A.made), flush=True)


while time.time() - t0 < secs:
    if A.made - A.cleared > LIMIT:
        A.memo.clear(); A.Ls.clear(); A.cleared = A.made
    J = max(J0, rec.bit_length() - SLACK)
    t, h = A.get(J, st)
    if h:
        show('BEFORE')
        print('HALT after', rec + h[1], 'records', h[0][2][:30], t.halt[2], flush=True)
        break
    st, s = apply(t, st)
    steps += s; rec += t.n
    if t.resets or time.time() - last > PRINT:
        resets += t.resets
        show('reset' if t.resets else 'at')
        last = time.time()
show('END')
print('STATE', repr((tuple(st[0]), st[1], st[2], steps, rec, resets)), flush=True)
