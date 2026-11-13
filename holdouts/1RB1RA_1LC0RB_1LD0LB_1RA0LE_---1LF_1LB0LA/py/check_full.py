"""Check the reduced phase map (py/drive.py output) against full-size phases: run c/phase.c with the true z for the
first N phases and compare P' and z'.  Prints the step count at each phase start (bbchallenge steps from blank tape).

usage: python3 py/check_full.py DRIVE_OUT N [PHASE_BINARY]
"""
import subprocess, sys
from itertools import groupby


def rle(P):
    return ' '.join(f"{k}^{len(list(g))}" for k, g in groupby(P))


def zmap(z):
    k, r = divmod(z, 4)
    return 6 * k + 1 if r == 1 else 6 * k + 7


rows = [l.split() for l in open(sys.argv[1]) if l[0].isdigit()]
n = int(sys.argv[2])
p = subprocess.Popen([sys.argv[3] if len(sys.argv) > 3 else './phase'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
P, z, steps = '1' * 14, 11, 218       # the first phase start: 1^14 0^11 B>0 at step 218
for i in range(n):
    p.stdin.write(f"{P} {z}\n"); p.stdin.flush()
    r = p.stdout.readline().split()
    assert r[0] != 'HALT'
    P2, z2, s = r[0], int(r[1]), int(r[3])
    row = rows[i]
    assert rle(P2) == ' '.join(row[5:]) and z2 == zmap(z) + int(row[2]), i
    steps += s
    print(i, 'ok, next phase starts at step', steps, 'z =', z2, flush=True)
    P, z = P2, z2
