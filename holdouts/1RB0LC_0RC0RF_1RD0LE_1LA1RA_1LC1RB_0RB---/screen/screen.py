#!/usr/bin/env python3
"""The family screen of F09 ("bouncers over lists of counters, not yet classified"): how long is the shortest
description of the tape, and does it grow?

For a machine, `dump.c` runs it from blank tape and prints the tape at the first new leftmost and the first new
rightmost cell after each threshold 10^6 * 4^k.  Each tape is compressed twice:

  level 1  greedy tandem repeats of the cells: a word of at most 40 cells repeated at least 3 times becomes one token
           `(w)^k`; every other cell is a token of its own.   raw = cells in no repeat, reps = number of repeats.
  level 2  the same on the list of level-1 tokens (a group of at most 60 tokens repeated at least twice, covering at
           least 4 tokens, becomes one token).              tok2 = number of level-2 tokens.

A tape that is a few growing periodic blocks and a bounded rest keeps raw, reps and tok2 bounded while its length
grows (family F01); a list of counters shows tok2 growing slowly; a sea of defects shows tok2 proportional to the
length (F11).  The numbers are a description of one run, not a result about the machine.

usage: python3 screen.py MACHINE [STEPS]      one machine (default 2e10 steps, about a minute)
       python3 screen.py --check              compare a 10^8-step run of every machine in screen.json with the file
       python3 screen.py --show MACHINE SIDE  the compressed tape at the last record of that side (L or R)
"""
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))


def compress(s, maxp=40, minrep=3):
    out, i, n, raw = [], 0, len(s), 0
    while i < n:
        best = None
        for p in range(1, maxp + 1):
            if i + p * minrep > n:
                break
            w, k = s[i:i + p], 1
            while s.startswith(w, i + k * p):
                k += 1
            if k >= minrep and (best is None or k * p > best[0] * best[1] + p):
                best = (p, k)
        if best:
            p, k = best
            out.append((s[i:i + p], k))
            i += p * k
        else:
            out.append((s[i], 1))
            raw += 1
            i += 1
    return out, raw


def tok_compress(toks, maxp=60, minrep=2):
    out, i, n = [], 0, len(toks)
    while i < n:
        best = None
        for p in range(1, maxp + 1):
            if i + p * minrep > n:
                break
            if toks[i:i + p] != toks[i + p:i + 2 * p]:
                continue
            k = 2
            while toks[i + k * p:i + (k + 1) * p] == toks[i:i + p]:
                k += 1
            if best is None or k * p > best[0] * best[1]:
                best = (p, k)
        if best and best[0] * best[1] >= 4:
            p, k = best
            out.append((tuple(toks[i:i + p]), k))
            i += p * k
        else:
            out.append((toks[i], 1))
            i += 1
    return out


def fmt(t):
    return t[0] if t[1] == 1 else '(%s)^%d' % t


def row(line):
    side, t, state, length, cells = line.split()
    out, raw = compress(cells)
    toks = [fmt(x) for x in out]
    reps = [len(w) * k for w, k in out if k > 1]
    return dict(side=side, t=int(t), len=int(length), raw=raw, reps=len(reps), tok1=len(toks),
                tok2=len(tok_compress(toks)), big=round(max(reps or [0]) / len(cells), 3))


def show(line):
    out, _ = compress(line.split()[4])
    o2 = tok_compress([fmt(x) for x in out])
    return ' '.join(('[' + ' '.join(w) + ']^%d' % k) if k > 1 else w for w, k in o2)


def dump(machine, steps):
    exe = os.path.join(tempfile.gettempdir(), 'f09_dump')
    subprocess.run(['gcc', '-O2', '-o', exe, os.path.join(HERE, 'dump.c')], check=True)
    r = subprocess.run([exe, machine, str(int(steps)), '1000000', '4'], stdout=subprocess.PIPE,
                       stderr=subprocess.DEVNULL, text=True)
    return [x for x in r.stdout.splitlines() if x and x[0] in 'LR']


def main(argv):
    if argv and argv[0] == '--check':
        ref = json.load(open(os.path.join(HERE, 'screen.json')))
        bad = 0
        for m, rows in sorted(ref.items()):
            got = [row(x) for x in dump(m, 1e8)]
            want = [r for r in rows if r['t'] <= 1e8][:len(got)]
            ok = got[:len(want)] == want and len(want) > 0
            bad += not ok
            print(m, 'ok' if ok else 'DIFFERENT', len(want), 'records')
        return 1 if bad else 0
    if argv and argv[0] == '--show':
        lines = [x for x in dump(argv[1], float(argv[3]) if len(argv) > 3 else 2e10) if x[0] == argv[2]]
        print(lines[-1].split()[1], show(lines[-1]))
        return 0
    m = argv[0]
    for x in dump(m, float(argv[1]) if len(argv) > 1 else 2e10):
        r = row(x)
        print('%s t=%.1e len=%d raw=%d reps=%d tok1=%d tok2=%d big=%.2f'
              % (r['side'], r['t'], r['len'], r['raw'], r['reps'], r['tok1'], r['tok2'], r['big']))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
