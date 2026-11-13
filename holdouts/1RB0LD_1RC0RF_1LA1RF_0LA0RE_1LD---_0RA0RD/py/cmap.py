#!/usr/bin/env python3
"""The draining law of 1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD (c2) and of its mirror image
1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB (c1, the same machine started in state E, left and right swapped),
checked against the direct simulator.

At the moments the head writes a new cell at the growing end in state D (c2; the same moment of c1 mirrored), the
tape read from the far end is   6 3^x1 9 3^x2 9 ... 9 3^xm TAIL   (runs of 1s, single 0s not written): blocks of
111 separated by single 0s, cut into segments by markers 1^9.  These moments come in cycles of three; at the first
moment of each cycle (TAIL = 12) the law is

    x_(m-j+1)  loses exactly 2 * 3^j  per cycle    (j = 1 for the segment next to the growing end, 2 for the one
                                                  before it, ...),
    except near the far end, where new segments are made (the generator).

It holds while no segment near the growing end runs out; when one does (a "collapse") the end segments merge and the
law starts again with fewer segments.  This script checks, for every pair of consecutive cycles in a run, how many
segments from the growing end obey the law, and prints the list at each cycle.

usage: python3 cmap.py [c2|c1] [STEPS]       (default c2 4.5e9)
"""
import os, re, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
B1 = os.path.join(HERE, '..', '..', '1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---')
MACH = {'c2': ('1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD', 'R'),
        'c1': ('1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB', 'L')}


def run(name, steps):
    m, side = MACH[name]
    exe = os.path.join(tempfile.gettempdir(), 'g01_evrun')
    subprocess.run(['gcc', '-O2', '-o', exe, os.path.join(B1, 'c', 'evrun.c')], check=True)
    out = subprocess.run([exe, m, str(int(float(steps))), 'rec', side, '100000000'], capture_output=True, text=True,
                         check=True).stdout
    cycles = []
    for line in out.split('\n'):
        f = line.split()
        if len(f) < 4 or not f[0].isdigit():
            continue
        toks = f[2:]
        if side == 'L':
            toks = toks[::-1]           # mirror: read from the far (right) end
        st = f[1]
        if st != ('D' if name == 'c2' else 'B'):
            continue
        # strip the head token and the cell next to it
        body = [t for t in toks if not t.startswith('|')]
        if not body or body[0] != '6' or body[-1] != 'z1' or len(body) < 3 or body[-2] != '12':
            continue
        L = [1 if t == '3' else int(t[2:]) for t in body[1:-2] if re.fullmatch(r'3(\^\d+)?', t)]
        cycles.append((int(f[0]), L))
    return cycles


if __name__ == '__main__':
    name = sys.argv[1] if len(sys.argv) > 1 else 'c2'
    steps = sys.argv[2] if len(sys.argv) > 2 else '4.5e9'
    cyc = run(name, steps)
    bad = 0
    for (t0, A), (t1, B) in zip(cyc, cyc[1:]):
        ok = 0
        for j in range(1, min(len(A), len(B)) + 1):
            if A[-j] - B[-j] == 2 * 3 ** j:
                ok += 1
            else:
                break
        print(f'{t1:>14} {B}   law holds for the last {ok} of {len(B)} segments')
        if ok < 2 and min(len(A), len(B)) >= 2:
            bad += 1
    print(f'{len(cyc)} cycles; {bad} cycle steps where the law fails for the last two segments (collapses)')
