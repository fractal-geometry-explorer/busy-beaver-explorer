"""Run the family checks for this machine (the scripts live in the family lead's py/ folder):

  check_rl.py  the run-length simulator c/rl.c agrees with the plain simulation at every sweep end (10^8 steps)
  model.py     every sweep end to 10^10 steps follows the two regular rules, or is a merge
  merges.py    none of the 48 merges of two markers with long blocks around them halts

usage: python3 py/check.py [MODEL_STEPS]   (default 1e10; the README quotes 1e11)
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
M = os.path.basename(os.path.dirname(HERE))
LEAD = '1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LC---'
PY = os.path.join(os.path.dirname(os.path.dirname(HERE)), LEAD, 'py')
steps = sys.argv[1] if len(sys.argv) > 1 else '1e10'
for script, args in (('check_rl.py', [M, '1e8']), ('model.py', [M, steps]), ('merges.py', [M])):
    print('==', script, *args, flush=True)
    r = subprocess.run([sys.executable, os.path.join(PY, script)] + args, cwd=PY)
    if r.returncode:
        sys.exit(f'{script} failed')
print('ALL FAMILY CHECKS RAN')
