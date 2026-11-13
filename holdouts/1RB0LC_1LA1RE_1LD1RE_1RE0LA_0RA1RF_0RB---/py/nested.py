"""Nested phases of 1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---: from Y(n, t) = C> (100)^n T with n odd (T = 1 or 101)
to the next single-number event X(n', t') / Y(n', t') (C helper ../c/single.c).  Checks the closed forms

    n = 4i+1:  Y(n, t) -> X(9i + 9,   t xor [i odd])     (5 C-left-end events)
    n = 8i+7:  Y(n, t) -> X(27i + 36, t xor [i odd])     (8 events)

and that every odd n < N comes back to the single-number form (no halt).   python3 nested.py N"""
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
N = int(sys.argv[1]) if len(sys.argv) > 1 else 400
d = tempfile.mkdtemp()
exe = os.path.join(d, 'single')
subprocess.check_call(['gcc', '-O2', '-o', exe, os.path.join(HERE, '..', 'c', 'single.c')])
P = subprocess.Popen([exe, '100000000000'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
bad = back = 0
deep = {}
for n in range(1, N, 2):
    for t in (0, 1):
        P.stdin.write('100' * n + ('101' if t else '1') + '\n')
        f = P.stdout.readline().split()
        if f[0] not in 'XY':
            print('n=%d t=%d: %s' % (n, t, ' '.join(f)))
            bad += 1
            continue
        back += 1
        got = (f[0], int(f[1]), int(f[2]))
        if n % 4 == 1:
            i = n // 4
            if got != ('X', 9 * i + 9, t ^ (i % 2)):
                bad += 1; print('differs', n, t, got)
        elif n % 8 == 7:
            i = n // 8
            if got != ('X', 27 * i + 36, t ^ (i % 2)):
                bad += 1; print('differs', n, t, got)
        else:
            deep[(n, t)] = (got, int(f[4]))
print('odd n < %d: %d of %d nested phases return to single-number form; closed forms: %d differ' %
      (N, back, 2 * len(range(1, N, 2)), bad))
print('n = 8i+3 (deeper nesting), first cases:', sorted(deep.items())[:8])
sys.exit(1 if bad else 0)
