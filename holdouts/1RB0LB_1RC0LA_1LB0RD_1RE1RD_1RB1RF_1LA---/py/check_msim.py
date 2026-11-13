#!/usr/bin/env python3
"""Check the macro simulator c/msim.c against the direct simulator tools/c/tm.h: run msim to about N steps, then run
the direct simulator exactly as many steps and compare state, head position and tape (zeros at the ends trimmed).

usage: python3 check_msim.py [STEPS]     (default 1e9; the four machines of families b and c of this group)"""
import os, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
MACHINES = ['1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---', '1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---',
            '1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD', '1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB']


def build(src, name):
    exe = os.path.join(tempfile.gettempdir(), 'g01_' + name)
    subprocess.run(['gcc', '-O2', '-o', exe, src], check=True)
    return exe


def expand_rle(tokens):
    cells, head = [], None
    for t in tokens:
        if '>' in t:
            st, v = t.split('>'); head = (len(cells), st); t = v
        if '^' in t:
            v, n = t.split('^'); cells += [v] * int(n)
        else:
            cells.append(t)
    return ''.join(cells), head


def trim(s, h):
    l = len(s) - len(s.lstrip('0'))
    return s.strip('0'), h - l


def check(m, steps, msim, tmrun):
    o = subprocess.run([msim, m, '4', str(steps), '-', str(10 ** 15)], capture_output=True, text=True,
                       check=True).stdout.strip().split('\n')[-1].split()
    n, st = int(o[2]), o[3]
    i = o.index('|')
    ex = lambda ts: ''.join(t.split('^')[0] * int(t.split('^')[1]) if '^' in t else t for t in ts)
    left, right = ex(o[4:i]), ex(o[i + 1:])
    h = len(left) if st[1] == '>' else len(left) - 1
    d = subprocess.run([tmrun, m, str(n), 'every', str(n)], capture_output=True, text=True, check=True).stdout.split('\n')[0].split()
    tape, (hd, sd) = expand_rle(d[1:])
    ok = trim(left + right, h) == trim(tape, hd) and st[0] == sd
    print(f'{m}: {n} steps, macro and direct {"agree" if ok else "DIFFER"}')
    return ok


if __name__ == '__main__':
    steps = sys.argv[1] if len(sys.argv) > 1 else '1e9'
    msim = build(os.path.join(HERE, '..', 'c', 'msim.c'), 'msim')
    tmrun = build(os.path.join(ROOT, 'tools', 'c', 'tmrun.c'), 'tmrun')
    sys.exit(0 if all([check(m, steps, msim, tmrun) for m in MACHINES]) else 1)
