#!/usr/bin/env python3
"""Law events of the nested ternary counter 1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA--- (b1) and of its twin
1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC--- (b2), from c/msimev.c (exact right records), and the general form of the
law of py/bmap.py.

An event is a step at which the head moves onto a new rightmost cell in state D or F with the tape (runs of 1s,
single 0s not written)  2 3^16 5 3 5  3^a1 5 3^a2 5 ... 5 3^am  TAIL:
    P: state D, TAIL = 1        Q: state D, TAIL = z1 (two 0s)        R: state F, TAIL = 2
The list is [a1, ..., am]: a1 = g the generator, a2..a(m-1) the segments, am = c the end counter.

General law (bmap.py's P_n, Q_n, R_n are the case g = g_n, segments = y_n(j)): with s = m - 2 segments,
    birth  P -> Q:  [g, y1..ys, c] -> [2*3^(s+4) - 28, g - 3^(s+1) + 1, y1 - 3^s, ..., ys - 3, c]
                    (in bmap.py's regime g = 2*3^(s+4) - 28 already, so the generator looks unchanged; after a
                    collapse it is not, and the birth resets it: seen in every reduced run and in the full run)
    drain  Q -> R and R -> P:  [g, y1..ys, c] -> [g + 2*3^(s+3), y1 - 3^s, ..., ys - 3, c - 1]
i.e. a segment with j segments on its right loses 3^(j+1) at every event, the end counter 1 at every drain, and
the generator gains 2*3^(s+3) at every drain.
"""
import os, re, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from m2runs import convert, fmt

MACH = {'b1': ('1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---', 161),
        'b2': ('1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---', 38)}
PREFIX = ['2', '3^16', '5', '3', '5']


def exe(name):
    out = os.path.join(tempfile.gettempdir(), 'g01_' + name)
    src = os.path.join(HERE, '..', 'c', name + '.c')
    if not os.path.exists(out) or os.path.getmtime(out) < os.path.getmtime(src):
        subprocess.run(['gcc', '-O2', '-o', out, src], check=True)
    return out


def birth(L):
    g, ys, c = L[0], L[1:-1], L[-1]
    s = len(ys)
    return [2 * 3 ** (s + 4) - 28, g - 3 ** (s + 1) + 1] + [y - 3 ** (s - i) for i, y in enumerate(ys)] + [c]


def drain(L):
    g, ys, c = L[0], L[1:-1], L[-1]
    s = len(ys)
    return [g + 2 * 3 ** (s + 3)] + [y - 3 ** (s - i) for i, y in enumerate(ys)] + [c - 1]


NEXT = {'P': ('Q', birth), 'Q': ('R', drain), 'R': ('P', drain)}


def suffix_cells(toks, n=12):
    out = ''
    for t in reversed(toks):
        w, c = (t.split('^')[0], int(t.split('^')[1])) if '^' in t else (t, 1)
        while c > 0 and len(out) < n:
            out = w + out
            c -= 1
        if len(out) >= n:
            break
    return out


def parse_event(line):
    """'STEPS S> tokens | tokens' (c/msimev.c) -> (steps, state, kind, list); kind None when it is no law event"""
    f = line.split()
    if len(f) < 3 or not f[0].isdigit():
        return None
    st = f[1][0]
    toks = f[2:f.index('|')] if '|' in f else f[2:]
    while toks and set(toks[0].split('^')[0]) == {'0'}:
        toks.pop(0)
    suf = suffix_cells(toks)
    kind = None
    if st == 'D' and suf.endswith('11101'):
        kind = 'P'
    elif st == 'D' and suf.endswith('01110'):
        kind = 'Q'
    elif st == 'F' and suf.endswith('111011'):
        kind = 'R'
    rt = fmt(convert(toks)).split()
    while rt and rt[0].startswith('z'):
        rt.pop(0)
    if kind is None or rt[:5] != PREFIX:
        return (int(f[0]), st, None, ' '.join(rt[-8:]))
    body = rt[5:]
    if kind in 'PR':
        body = body[:-1]          # the tail run 1 or 2
    L = []
    i = 0
    while i < len(body):
        t = body[i]
        if t == '3' or re.fullmatch(r'3\^\d+', t):
            L.append(1 if t == '3' else int(t[2:]))
            i += 1
            if i < len(body):
                if body[i] != '5':
                    return (int(f[0]), st, None, ' '.join(rt[-8:]))
                i += 1
                if i == len(body):
                    L.append(0)
        elif t == '5':
            L.append(0)
            i += 1
        elif re.fullmatch(r'5\^\d+', t):
            L += [0] * (int(t[2:]) - 1)
            i += 1
            if i == len(body):
                L.append(0)
        else:
            return (int(f[0]), st, None, ' '.join(rt[-8:]))
    return (int(f[0]), st, kind, L)


def run_events(mach, cfg, steps, seconds=1e9, maxev=-1, states='DF'):
    args = [exe('msimev'), mach, '4', str(steps), cfg, states, str(seconds), str(maxev)]
    p = subprocess.Popen(args, stdout=subprocess.PIPE, text=True)
    for line in p.stdout:
        if line.startswith('END') or line.startswith('HALT') or line.startswith('LOOP') or line.startswith('JUMP'):
            yield ('END', line.strip())
            continue
        e = parse_event(line)
        if e:
            yield e
    p.wait()


def config(runs, state='D'):
    """a start configuration for msim from a list of runs of 1s (single 0s between), head on the 0 after them"""
    cells = '0' * 8 + '0'.join('1' * r for r in runs)
    return '%s %d %s0\n' % (state, len(cells), cells)


def rle_config(runs, path, state='D', K=4):
    """the configuration 1^r0 0 1^r1 0 ... 1^rlast 0 with the head on that last 0 (state STATE, facing right),
    written as blocks of K cells with counts for c/msimev.c ('rle:' start).  runs: list of (r, multiplicity)."""
    total = sum((r + 1) * n for r, n in runs) + 8
    pad = (-(total - 1)) % K + 8
    out = []            # (word, count)
    buf = '0' * pad

    def flush_blocks():
        nonlocal buf
        while len(buf) >= K:
            w = buf[:K]
            buf = buf[K:]
            if out and out[-1][0] == w:
                out[-1][1] += 1
            else:
                out.append([w, 1])
    for r, n in runs:
        unit = '1' * r + '0'
        if n * len(unit) < 4 * K or len(unit) != K:
            for _ in range(n):
                buf += unit
                flush_blocks()
            continue
        # periodic stretch with period K: fill to a boundary, then whole blocks, then the remainder
        p = len(buf) % K
        cells = n * K
        lead = (K - p) % K
        buf += (unit * 2)[:lead]
        flush_blocks()
        rot = (unit * 2)[lead:lead + K]
        whole = (cells - lead) // K
        rest = (cells - lead) - whole * K
        if whole:
            if out and out[-1][0] == rot:
                out[-1][1] += whole
            else:
                out.append([rot, whole])
        buf += (rot * 2)[:rest]
        flush_blocks()
    # the head cell is the last 0 written; total cells = len(blocks)*K + len(buf)
    ncells = sum(c for _, c in out) * K + len(buf)
    head = ncells - 1
    assert head % K == 0, (head, K)
    buf += '0' * ((-len(buf)) % K)
    flush_blocks()
    with open(path, 'w') as f:
        f.write('%s %d %d\n' % (state, head // K, len(out)))
        for w, c in out:
            f.write('%s %d\n' % (w, c))
    return 'rle:' + path
