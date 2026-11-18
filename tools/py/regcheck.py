#!/usr/bin/env python3
"""Check tools/py/bbtools/regaccel.py against a direct run, cell for cell.

Every time the accelerated run is at the top level with the head facing blank tape on the right (up to STEPS
steps, at most 3,000 times), its state and the whole tape are recorded; tools/c/snap.c runs the machine directly to
the same step counts and prints the same; they must agree.

    python3 tools/py/regcheck.py MACHINE K STEPS SECONDS [mir]      # prints one JSON line
"""
import json
import os
import subprocess
import sys
import tempfile
import threading

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'bbtools'))
import regaccel as G  # noqa: E402


def main():
    m, K, N, sec = sys.argv[1], int(sys.argv[2]), int(float(sys.argv[3])), float(sys.argv[4])
    mir = 'mir' in sys.argv[5:]
    mm = G.mirror(m) if mir else m
    exe = os.path.join(tempfile.gettempdir(), 'bb_snap')
    subprocess.run(['gcc', '-O2', '-o', exe, os.path.join(HERE, '..', 'c', 'snap.c')], check=True)
    rec = []
    ob = G.Sim.basic

    def basic(self, L, R, b, q, d, ctx):
        if ctx is None and d == 1 and len(R) == 1 and R is self.R and 0 < self.steps <= N and len(rec) < 3000:
            cells = ''.join(format(s, '0%db' % K) * c for s, c in L[1:]).lstrip('0')
            rec.append((self.steps, 'ABCDEFGH'[q], cells))
        return ob(self, L, R, b, q, d, ctx)
    G.Sim.basic = basic
    sys.setrecursionlimit(1000000)
    threading.stack_size(512 * 1024 * 1024)
    out = {}

    def go():
        s = G.Sim(mm, K)
        s.run(sec, max_steps=N)
        out['s'] = s
    th = threading.Thread(target=go)
    th.start()
    th.join()
    res = subprocess.run([exe, mm], input=''.join('%d\n' % r[0] for r in rec), capture_output=True,
                         text=True).stdout.split('\n')
    bad = 0
    for r, line in zip(rec, res):
        p = line.split(' ')
        if not (len(p) == 4 and int(p[0]) == r[0] and p[1] == r[1] and p[2] == r[2] and p[3] == '1'):
            bad += 1
    print(json.dumps(dict(machine=m, orient='mir' if mir else 'fwd', K=K, snap_steps=N,
                          snapshots=len(rec), snap_bad=bad, last=rec[-1][0] if rec else 0)))
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
