#!/usr/bin/env python3
"""Deep exact runs of the Skelet 1-like counter family (F06) with the macro simulator c/msim.c.

For each machine: try block sizes K = 2..10 for a few seconds each, keep the K that gets furthest, run it for SECONDS
of wall-clock time from blank tape, and record how many machine steps were simulated without a halt (or the halt).
msim is exact (every macro step is a run of the machine, counted step for step); `verify` checks it per machine, at
the block size used, against the direct simulator tools/c/tmrun.c: same state, head position and tape after the same
number of steps.

    python3 py/deep.py run SECONDS [TRIAL_SECONDS [WORKERS]]   # all machines of data/deep.json not yet done at SECONDS
    python3 py/deep.py verify [STEPS]                          # macro against direct, default 2e9 steps
    python3 py/deep.py table                                   # the results

Results are kept in data/deep.json: {machine: {K, seconds, result, steps, verified}}.  A machine whose tape does not
compress at any K ends early with result "cap" (4 million runs); its step count is still exact.
"""
import json
import os
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
DATA = os.path.join(HERE, '..', 'data', 'deep.json')


def build(src, name):
    exe = os.path.join(tempfile.gettempdir(), 'f06_' + name)
    subprocess.run(['gcc', '-O2', '-o', exe, src], check=True)
    return exe


def last_line(msim, m, K, wall, steps='1e36'):
    out = subprocess.run([msim, m, str(K), steps, '-', '0', 'r', str(wall)], capture_output=True, text=True).stdout
    return out.strip().split('\n')[-1].split() if out.strip() else []


def outcome(p):
    """(result, steps) of the last line of msim."""
    if not p:
        return 'none', 0
    if p[0] == 'HALT':
        return 'halt', int(p[1])
    if p[0] == 'LOOP':
        return 'loop', int(p[1])
    if p[1] == 'cap':
        return 'cap', int(p[3])
    return 'running', int(p[2])


def deep(msim, m, seconds, trial):
    best = None
    for K in range(2, 11):
        r = outcome(last_line(msim, m, K, trial))
        if r[0] == 'halt':
            return dict(K=K, seconds=trial, result='halt', steps=r[1])
        if r[0] in ('running', 'cap') and (best is None or r[1] > best[1]):
            best = (K, r[1])
    r = outcome(last_line(msim, m, best[0], seconds))
    return dict(K=best[0], seconds=seconds, result=r[0], steps=r[1])


def load():
    return json.load(open(DATA))


def save(d):
    with open(DATA, 'w') as f:
        json.dump(d, f, indent=1, sort_keys=True)
        f.write('\n')


def run(seconds, trial, workers):
    msim = build(os.path.join(HERE, '..', 'c', 'msim.c'), 'msim')
    d = load()
    todo = [m for m in d if d[m].get('seconds', 0) < seconds and d[m].get('result') != 'halt']
    with ThreadPoolExecutor(workers) as ex:
        for m, r in zip(todo, ex.map(lambda m: deep(msim, m, seconds, trial), todo)):
            r['verified'] = d[m].get('verified') if d[m].get('K') == r['K'] else None
            d[m] = r
            save(d)
            print(m, r, flush=True)


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
    return s.strip('0'), h - (len(s) - len(s.lstrip('0')))


def verify_one(msim, tmrun, m, K, steps):
    o = last_line(msim, m, K, 1e9, steps)
    if o[0] != 'END' or o[1] == 'cap':
        return None
    n, st = int(o[2]), o[3]
    i = o.index('|')
    ex = lambda ts: ''.join(t.split('^')[0] * int(t.split('^')[1]) if '^' in t else t for t in ts)
    left, right = ex(o[4:i]), ex(o[i + 1:])
    h = len(left) if st[1] == '>' else len(left) - 1
    dd = subprocess.run([tmrun, m, str(n), 'every', str(n)], capture_output=True, text=True, check=True)
    dd = dd.stdout.split('\n')[0].split()
    tape, (hd, sd) = expand_rle(dd[1:])
    return n if trim(left + right, h) == trim(tape, hd) and st[0] == sd else -n


def verify(steps):
    msim = build(os.path.join(HERE, '..', 'c', 'msim.c'), 'msim')
    tmrun = build(os.path.join(ROOT, 'tools', 'c', 'tmrun.c'), 'tmrun')
    d, bad = load(), 0
    for m in d:
        if 'K' not in d[m]:
            continue
        n = verify_one(msim, tmrun, m, d[m]['K'], steps)
        if n is None or n < 0:
            bad += 1
            print(m, 'K =', d[m]['K'], 'DIFFER' if n else 'no comparison', flush=True)
            d[m]['verified'] = None
        else:
            print(m, 'K =', d[m]['K'], ': macro and direct agree after', n, 'steps', flush=True)
            d[m]['verified'] = n
        save(d)
    return bad


def table():
    d = load()
    for m in sorted(d, key=lambda m: d[m].get('steps', 0)):
        r = d[m]
        print('%s  K=%-2s %-8s %.2e steps in %ss, checked against the direct run to %s' % (
            m, r.get('K'), r.get('result'), r.get('steps', 0), r.get('seconds'), r.get('verified')))


if __name__ == '__main__':
    if sys.argv[1] == 'run':
        a = sys.argv[2:]
        run(float(a[0]), float(a[1]) if len(a) > 1 else 6, int(a[2]) if len(a) > 2 else 2)
    elif sys.argv[1] == 'verify':
        sys.exit(1 if verify(sys.argv[2] if len(sys.argv) > 2 else '2e9') else 0)
    else:
        table()
