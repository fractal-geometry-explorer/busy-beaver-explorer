"""The wall of 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE: a fixed stretch of 1,573 cells at the right end that the
head rewrites like a counter.

At each visit of the head, in state C, to the left end of the tape where the tape is F>0 (01101)^n W with W of
exactly 1,573 cells (once per sweep), compare W with the previous W: the changes always start at cell 44 of W and
reach further now and then, like the carries of a counter.  Prints every new record of the deepest change.

usage: python3 wall.py [STEPS] [FROM]   (defaults 2e10 2e7)
"""
import os, subprocess, sys, tempfile

M = '1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE'
HERE = os.path.dirname(os.path.abspath(__file__))


def main(steps, frm):
    exe = os.path.join(tempfile.gettempdir(), 'walldump_m6')
    subprocess.run(['gcc', '-O2', '-o', exe, os.path.join(HERE, '../c/walldump.c')], check=True)
    p = subprocess.Popen([exe, M, str(int(steps)), 'C', '01101', '1573', '1000000000', str(int(frm))],
                         stdout=subprocess.PIPE, text=True)
    prev, deepest, n, first = None, 0, 0, 10 ** 9
    for line in p.stdout:
        s, w = line.split()
        if prev:
            d = [j for j in range(len(w)) if w[j] != prev[j]]
            if d:
                first = min(first, d[0])
                if d[-1] > deepest:
                    deepest = d[-1]
                    print(f'sweep {n} (step {s}): deepest change so far at cell {deepest}')
        prev, n = w, n + 1
    print(f'{n} sweeps with a wall of 1,573 cells; changes never start before cell {first}')


if __name__ == '__main__':
    a = sys.argv[1:]
    main(float(a[0]) if a else 2e10, float(a[1]) if len(a) > 1 else 2e7)
