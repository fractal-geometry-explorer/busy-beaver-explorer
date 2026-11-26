#!/usr/bin/env python3
"""Checks for tools/segreplay.  Run from anywhere: python3 tools/segreplay/test_segreplay.py [--coq]

1. Every description in specs/ made from a Lean file is what lean2spec.py writes today.
2. For every description, the generated C runner and the Python reference interpreter agree on the first
   30,000 visits.
3. With --coq (needs coqc 8.20): Core.v and every generated Map.v compile, i.e. the generated proofs that the
   machine-integer map equals the map on integers go through.
"""
import json, os, subprocess, sys, tempfile
T = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, T)
from segreplay import Spec

def main():
    specs = sorted(f for f in os.listdir(os.path.join(T, 'specs')) if f.endswith('.json'))
    tmp = tempfile.mkdtemp()
    bad = 0
    for f in specs:
        path = os.path.join(T, 'specs', f)
        d = json.load(open(path))
        src = d.get('source', '')
        if src.endswith('.lean'):
            r = subprocess.run([sys.executable, os.path.join(T, 'lean2spec.py'), src, d['lean_def'], d['lean_start'], d['machine']],
                               capture_output=True, text=True, cwd=os.path.join(T, '..', '..'))
            if r.returncode != 0 or json.loads(r.stdout) != d:
                print('FAIL lean2spec', f); bad += 1
        spec = Spec(d)
        c = os.path.join(tmp, 'run.c'); exe = os.path.join(tmp, 'run')
        open(c, 'w').write(spec.c_runner())
        subprocess.run(['gcc', '-O1', '-o', exe, c, '-lm'], check=True)
        N = 30000
        lines = subprocess.run([exe, str(N), '1'], capture_output=True, text=True).stdout.splitlines()
        t, x = spec.frames.index(spec.start[0]), list(spec.start[1:])
        ok = True
        for i in range(N + 1):
            p = lines[i].split()
            if p[0] not in ('seg', 'halt') or int(p[1]) != i or int(p[2]) != t or [int(v) for v in p[3:]] != x:
                ok = False; break
            if p[0] == 'halt':
                break
            t, x = spec.py_step(t, x)
        print('ok  ' if ok else 'FAIL', 'C = Python,', i, 'visits:', f)
        bad += not ok
        if '--coq' in sys.argv:
            out = os.path.join(tmp, f[:-5]); os.makedirs(out)
            open(os.path.join(out, 'Map.v'), 'w').write(spec.coq_map())
            if not os.path.exists(os.path.join(T, 'coq', 'Core.vo')):
                subprocess.run(['coqc', '-Q', '.', 'SegReplay', 'Core.v'], cwd=os.path.join(T, 'coq'), check=True)
            r = subprocess.run(['coqc', '-Q', os.path.join(T, 'coq'), 'SegReplay', '-Q', out, 'M', os.path.join(out, 'Map.v')],
                               capture_output=True, text=True)
            print('ok  ' if r.returncode == 0 else 'FAIL', 'Map.v compiles:', f)
            bad += r.returncode != 0
    print('ALL OK' if not bad else '%d FAILED' % bad)
    return bad

if __name__ == '__main__':
    sys.exit(main())
