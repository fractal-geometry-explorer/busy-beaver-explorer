"""Every far-shape member of a route at one lane value, from the census outputs at R1, R2 (as shape.py), with its shape,
W mod 6 and mod 4, and its pullbacks.  usage: dump.py out name R1 R2 C c j Wexp"""
import sys, os, re, math
sys.path.insert(0, os.environ.get('FARLOOP', '.')); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from smallmod import solutions
from pullback import preds, shape
def classes(f):
    txt = open(f).read()
    return [(int(m.group(1)), int(m.group(2)), int(m.group(3))) for m in
            re.finditer(r'close R=\d+ D=\d+ a=.*? b=(\d+)\+\[0, (\d+)\] rounds=(\d+)', txt)]
out, name, R1, R2, C, c, j, Wexp = sys.argv[1], sys.argv[2], *map(int, sys.argv[3:9])
P = R2 - R1; lane = c * 2 ** j; Dof = lambda R: lane - C - 22 - 2 * R
A = classes(f'{out}/{name}_x{c}_{j}_R{R1}.txt'); B = classes(f'{out}/{name}_x{c}_{j}_R{R2}.txt')
for bA, M, rA in A:
    for bB, MB, rB in B:
        if MB != M: continue
        st = (bB - bA) % M
        ilo = max(0, -(-(769 - R1) // P)); ihi = (lane - C - 22 - 3 * R1 - 449) // (3 * P)
        Bmax = 49 * Dof(R1 + P * ilo) // 15 + 1
        for i, b in solutions(bA, st, M, Bmax, ilo, ihi, limit=10 ** 6):
            R = R1 + P * i; D = Dof(R); W = b + D
            if not (b >= 897 and D >= R + 449 and 15 * b <= 49 * D and W > 2 ** Wexp): continue
            print(name, i, R, b, W, f'{R/W:.5f}', f'{D/W:.4f}', W % 6, W % 4, ','.join(shape(b, W, R)) or '-', sep='\t')
