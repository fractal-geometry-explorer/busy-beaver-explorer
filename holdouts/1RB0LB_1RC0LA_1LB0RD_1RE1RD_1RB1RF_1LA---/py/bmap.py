#!/usr/bin/env python3
"""The regime law of 1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA--- (b1) and of 1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---
(b2, the same machine started in state B), checked against simulation.

At the moments the head writes a new cell on the right in state D or F, the tape is, in runs of 1s (single 0s between
runs not written):   2 3^16 5 3 5  3^a1 5 3^a2 5 ... 5 3^am  TAIL
i.e. blocks of 111 separated by single 0s, cut by markers 11111 into segments; the list L = [a1, ..., am] is the
state.  These moments come in a cycle of three, P_n, Q_n, R_n (n = -1, 0, 1, ...), with, for k = n + 1:

  P_n = [g_n, y_n(n), ..., y_n(0), c_n]   g_n = 2*3^(n+5) - 28,   y_n(j) = 3^(j+2) * (17 - n + j) - 27,
                                          c_n = c0 - 2n   (c0 = 161 for b1, 38 for b2)
  Q_n = [g, g - 3^(k+1) + 1, y_1 - 3^k, ..., y_k - 3, c]            (from P_n = [g, y_1..y_k, c])
  R_n = [a + 2*3^(k+4), b - 3^(k+1), z_1 - 3^k, ..., z_k - 3, c - 1]   (from Q_n = [a, b, z_1..z_k, c])
  P_(n+1) = the same step again from R_n.

The law holds while every subtraction leaves a count >= 0; y_n(0) = 9 (17 - n) - 27 is the first to give out:
y_13(0) = 9, y_14(0) = 0, and Q_14 would need y - 3 < 0.  So the regime ends at P_14, near 2.6e18 steps.

usage: python3 bmap.py [b1|b2] [direct STEPS | macro STEPS | saved FILE]
  direct: the C simulator c/evrun.c, every right record in state D or F compared with the law (default 1e9 steps);
  macro:  the macro simulator c/msim.c, every snapshot's list compared with the law (default 1e15 steps);
  saved:  the same check on a saved output of c/msim.c (data/b1_msim.txt, data/b2_msim.txt: runs to 2.8e17 steps).
"""
import os, re, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
CDIR = os.path.join(HERE, '..', 'c')
MACH = {'b1': ('1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---', 161),
        'b2': ('1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---', 38)}
PREFIX = ['2', '3^16', '5', '3', '5']


def build(name):
    out = os.path.join(tempfile.gettempdir(), 'g01_' + name)
    subprocess.run(['gcc', '-O2', '-o', out, os.path.join(CDIR, name + '.c')], check=True)
    return out


def law(c0, nmax):
    """The predicted lists in order: P_-1, Q_-1, R_-1, P_0, ..."""
    seq = []
    for n in range(-1, nmax + 1):
        k = n + 1
        g = 2 * 3 ** (n + 5) - 28
        ys = [3 ** (j + 2) * (17 - n + j) - 27 for j in range(n, -1, -1)]
        c = c0 - 2 * n
        P = [g] + ys + [c]
        Q = [g, g - 3 ** (k + 1) + 1] + [y - 3 ** (k - i) for i, y in enumerate(ys)] + [c]
        R = [Q[0] + 2 * 3 ** (k + 4), Q[1] - 3 ** (k + 1)] + [z - 3 ** (k - i) for i, z in enumerate(Q[2:-1])] + [c - 1]
        seq += [('P', n, P), ('Q', n, Q), ('R', n, R)]
    return seq


def parse_list(tokens):
    """[a1..am] from '2 3^16 5 3 5 3^a1 5 ... 3^am TAIL', or None."""
    if tokens[:5] != PREFIX:
        return None
    L, i = [], 5
    while i < len(tokens):
        t = tokens[i]
        if t == '3' or re.fullmatch(r'3\^\d+', t):
            L.append(1 if t == '3' else int(t[2:]))
            if i + 1 < len(tokens) and tokens[i + 1] == '5':
                i += 2
                continue
            break
        break
    return L


def check_direct(name, steps):
    m, c0 = MACH[name]
    exe = build('evrun')
    p = subprocess.run([exe, m, str(steps), 'rec', 'R', '100000000'], capture_output=True, text=True, check=True)
    seq = law(c0, 40)
    pos, n_ok, first = 0, 0, None
    for line in p.stdout.split('\n'):
        f = line.split()
        if len(f) < 3 or not f[0].isdigit() or f[1] not in 'DF':
            continue
        L = parse_list(f[2:])
        if L is None:
            continue
        tail = f[-2]
        kind = 'P' if (f[1] == 'D' and tail == '1') else 'Q' if (f[1] == 'D' and tail == 'z1') else 'R' if (f[1] == 'F' and tail == '2') else None
        if kind is None:
            continue
        if first is None:
            if L != seq[0][2]:
                continue          # before P_-1 (step 223270): the start-up
            first = int(f[0])
        if pos >= len(seq) or (kind, L) != (seq[pos][0], seq[pos][2]):
            print('MISMATCH at step', f[0], kind, L[:6], 'expected', seq[pos][0], seq[pos][1], seq[pos][2][:6])
            return False
        pos += 1; n_ok += 1
    print(f'{name}: {n_ok} events from step {first} to {steps} steps, all as the law says (last: {seq[pos-1][0]}_{seq[pos-1][1]})')
    return True


def check_macro(name, steps, saved=None):
    sys.path.insert(0, HERE)
    from m2runs import convert, fmt
    m, c0 = MACH[name]
    if saved:
        class p: stdout = open(saved).read()
    else:
        exe = build('msim')
        p = subprocess.run([exe, m, '4', str(steps), '-', '1'], capture_output=True, text=True, check=True)
    seq = [L for _, _, L in law(c0, 13)]
    seq_named = ['%s_%d' % (a, b) for a, b, _ in law(c0, 13)]
    pos, n, started = 0, 0, False
    for line in p.stdout.split('\n'):
        f = line.split()
        if len(f) < 3 or not f[0].isdigit():
            continue
        i = f.index('|')
        toks = [t for t in f[2:i] + f[i + 1:]]
        while toks and set(toks[0].split('^')[0]) == {'0'}: toks.pop(0)
        while toks and set(toks[-1].split('^')[0]) == {'0'}: toks.pop()
        rt = fmt(convert(toks)).split()
        while rt and rt[0].startswith('z'): rt.pop(0)
        L = parse_list(rt)
        # a snapshot is taken when the head enters a new block of 4 cells, a few steps away from the law's events:
        # the segments must be those of the current or the next law event, the last count (the one the head is
        # working on) within 2 of it
        same = lambda A, B: A[:-1] == B[:-1] and abs(A[-1] - B[-1]) <= 2
        if L is None or (not started and not same(L, seq[0])):
            continue
        started = True
        if same(L, seq[pos]):
            n += 1; continue
        # a law event can fall inside a block already visited, so it may have no snapshot of its own: step over one
        if pos + 1 < len(seq) and same(L, seq[pos + 1]):
            pos += 1; n += 1; continue
        if pos + 2 < len(seq) and same(L, seq[pos + 2]):
            pos += 2; n += 1; continue
        print('MISMATCH at', f[0], L[:5], '...', L[-3:], 'expected', seq[pos][:3], seq[pos][-3:])
        return False
    last = seq_named[pos]
    print(f'{name}: {n} macro snapshots{" in " + saved if saved else ""} all on the law, the last one {last}')
    return True


if __name__ == '__main__':
    name = sys.argv[1] if len(sys.argv) > 1 else 'b1'
    mode = sys.argv[2] if len(sys.argv) > 2 else 'direct'
    if mode == 'saved':
        sys.exit(0 if check_macro(name, 0, sys.argv[3]) else 1)
    steps = int(float(sys.argv[3])) if len(sys.argv) > 3 else (10 ** 9 if mode == 'direct' else 10 ** 15)
    ok = check_direct(name, steps) if mode == 'direct' else check_macro(name, steps)
    sys.exit(0 if ok else 1)
