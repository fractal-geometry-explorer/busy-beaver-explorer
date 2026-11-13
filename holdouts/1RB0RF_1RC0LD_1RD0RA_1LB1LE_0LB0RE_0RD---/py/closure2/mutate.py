"""Mutation test of the closed-set check: plant one defect at a time and run validate.py; every defect must be
reported (search not closed, or the real run leaves the node graph).  Results are appended to OUT as they come,
so the test can be continued after an interruption (finished defects are skipped).

usage (from the repo root): python3 holdouts/<M>/py/closure2/mutate.py MACHINE MAXSTEPS OUT.txt
"""
import os
import subprocess
import sys

DEFECTS = ['drop_remainder', 'first_shrink_only', 'no_zero_case', 'no_small_cases', 'grow_threshold',
           'flip_ratio', 'no_ratio']
HERE = os.path.dirname(os.path.abspath(__file__))


def main():
    M, mx, out = sys.argv[1:4]
    done = open(out).read() if os.path.exists(out) else ''
    for d in DEFECTS:
        if '[%s]' % d in done:
            continue
        env = dict(os.environ, DEFECT=d, TMAX='240')
        r = subprocess.run([sys.executable, os.path.join(HERE, 'validate.py'), M, mx], env=env, capture_output=True,
                           text=True)
        lines = [x[:400] for x in (r.stdout + r.stderr).strip().split('\n')]
        with open(out, 'a') as f:
            f.write('[%s]\n  %s\n' % (d, '\n  '.join(lines[:3] + lines[-1:])))


if __name__ == '__main__':
    main()
