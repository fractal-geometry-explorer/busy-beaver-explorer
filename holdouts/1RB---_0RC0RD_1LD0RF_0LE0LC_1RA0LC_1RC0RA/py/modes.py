"""The two working modes of 1RB---_0RC0RD_1LD0RF_0LE0LC_1RA0LC_1RC0RA at the right end, checked against the C
simulator, and the sequence of top blocks.

At every moment the head, in state F, is at the right end of the tape (reading blank), the tape ends in one of
    mode A:  ... 1^X (01)^Y 0 F>0                 next:  ... 1^(X-2) (01)^(Y+2) 0 F>0
    mode B:  ... 1^X (01)^Y 0010 (01)^Z 0 F>0     next:  ... 1^(X-4) (01)^(Y+2) 0010 (01)^(Z+1) 0 F>0
(the rest of the tape unchanged), or the top block is used up and the head rewrites the blocks before it (a pop).

usage: python3 modes.py [STEPS]   (default 1e9)
Prints the number of visits each mode rule predicts (checked: X >= 5 or 7 and the counts >= 2, so that the text
form is unambiguous), wrong predictions (none), the number of other visits (pops and small cases), and every new
top block of ones of 100 or more cells with the step it appears at.
"""
import os, re, subprocess, sys, tempfile

M = '1RB---_0RC0RD_1LD0RF_0LE0LC_1RA0LC_1RC0RA'
HERE = os.path.dirname(os.path.abspath(__file__))
RA = re.compile(r'^(.*) \(1\)\^(\d+) \(01\)\^(\d+) 0 F>0$')
RB = re.compile(r'^(.*) \(1\)\^(\d+) \(01\)\^(\d+) 0010 \(01\)\^(\d+) 0 F>0$')


def main(steps):
    exe = os.path.join(tempfile.gettempdir(), 'blocks_m2')
    subprocess.run(['gcc', '-O2', '-o', exe, os.path.join(HERE, '../c/blocks.c')], check=True)
    p = subprocess.Popen([exe, M, str(int(steps)), 'F', 'R', '2', '1'], stdout=subprocess.PIPE, text=True)
    prev = None
    na = nb = bad = other = 0
    tops = []
    for line in p.stdout:
        if line.startswith('halted'):
            print('HALTED', line.strip()); return 1
        if line.startswith('running'):
            break
        st, tape = line.rstrip('\n').split(' ', 1)
        tape = ' ' + tape
        if prev is not None:
            pst, pt = prev
            a, b = RA.match(pt), RB.match(pt)
            if b and int(b.group(2)) >= 7 and int(b.group(3)) >= 2 and int(b.group(4)) >= 2:
                exp = f'{b.group(1)} (1)^{int(b.group(2)) - 4} (01)^{int(b.group(3)) + 2} 0010 (01)^{int(b.group(4)) + 1} 0 F>0'
                nb += 1
                if exp != tape:
                    bad += 1; print('mode B mismatch at', st)
            elif a and int(a.group(2)) >= 5 and int(a.group(3)) >= 2:
                exp = f'{a.group(1)} (1)^{int(a.group(2)) - 2} (01)^{int(a.group(3)) + 2} 0 F>0'
                na += 1
                if exp != tape:
                    bad += 1; print('mode A mismatch at', st)
            else:
                other += 1
                for r, mode in ((RB, 'B'), (RA, 'A')):
                    m = r.match(tape)
                    if m and int(m.group(2)) >= 100:
                        tops.append((int(st), mode, int(m.group(2)), int(m.group(3))))
                        break
        prev = (st, tape)
    print(f'mode A visits predicted: {na}, mode B: {nb}, wrong: {bad}, other visits (pops, small cases): {other}')
    print('new top blocks of >= 100 ones (step, mode, ones, pairs):')
    for t in tops:
        print('  %d %s 1^%d (01)^%d' % t)
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main(float(sys.argv[1]) if len(sys.argv) > 1 else 1e9))
