#!/usr/bin/env python3
"""The macro simulator c/msim.c (a copy of holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/c/msim.c, unchanged) on
the G01 machines of the third pass, each with its own block size: run msim to about N steps, run the direct simulator
tools/c/tmrun.c exactly as many steps, and compare state, head position and tape (zeros at the ends trimmed).
Then `run` gives the "no halt in N steps" runs quoted in the READMEs.

usage: python3 check_msim.py check [STEPS]          (default 1e9)
       python3 check_msim.py run MACHINE STEPS      msim from blank tape with this machine's block size
"""
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
K = {  # block size per machine (the period of the words its tape is made of)
    '1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA': 6,
    '1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---': 4,
    '1RB0LA_0RC1RD_0LD1RE_1LA0RF_0RD0LD_1RD---': 6,
    '1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---': 6,
    '1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA---': 6,
    '1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD---': 6,
    '1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---': 6,
    '1RB0LE_1LC0RD_0RA1LD_0LC1RA_1LF1LA_---1LA': 6,
}


def build(src, name):
    exe = os.path.join(tempfile.gettempdir(), 'g01k_' + name)
    subprocess.run(['gcc', '-O2', '-o', exe, src], check=True)
    return exe


def expand_rle(tokens):
    cells, head = [], None
    for t in tokens:
        if '>' in t:
            st, v = t.split('>')
            head = (len(cells), st)
            t = v
        if '^' in t:
            v, n = t.split('^')
            cells += [v] * int(n)
        else:
            cells.append(t)
    return ''.join(cells), head


def trim(s, h):
    lead = len(s) - len(s.lstrip('0'))
    return s.strip('0'), h - lead


def msim_run(msim, m, steps):
    out = subprocess.run([msim, m, str(K[m]), str(steps), '-', str(10 ** 18)], capture_output=True, text=True,
                         check=True).stdout.strip().split('\n')[-1]
    return out


def check(m, steps, msim, tmrun):
    o = msim_run(msim, m, steps).split()
    n, st = int(o[2]), o[3]
    i = o.index('|')
    ex = lambda ts: ''.join(t.split('^')[0] * int(t.split('^')[1]) if '^' in t else t for t in ts)
    left, right = ex(o[4:i]), ex(o[i + 1:])
    h = len(left) if st[1] == '>' else len(left) - 1
    d = subprocess.run([tmrun, m, str(n), 'every', str(n)], capture_output=True, text=True,
                       check=True).stdout.split('\n')[0].split()
    tape, (hd, sd) = expand_rle(d[1:])
    ok = trim(left + right, h) == trim(tape, hd) and st[0] == sd
    print(f'{m} (blocks of {K[m]}): {n} steps, macro and direct {"agree" if ok else "DIFFER"}', flush=True)
    return ok


if __name__ == '__main__':
    a = sys.argv[1:] or ['check']
    msim = build(os.path.join(HERE, '..', 'c', 'msim.c'), 'msim')
    if a[0] == 'check':
        tmrun = build(os.path.join(ROOT, 'tools', 'c', 'tmrun.c'), 'tmrun')
        steps = a[1] if len(a) > 1 else '1e9'
        sys.exit(0 if all([check(m, steps, msim, tmrun) for m in K]) else 1)
    elif a[0] == 'run':
        print(msim_run(msim, a[1], a[2]))
