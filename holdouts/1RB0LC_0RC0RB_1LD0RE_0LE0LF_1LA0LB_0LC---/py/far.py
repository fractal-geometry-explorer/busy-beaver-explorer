"""Run a machine of the family far with c/rl.c and summarise: no halt, entries into F, the last tape.

usage: python3 far.py MACHINE [STEPS]   (default 1e16; about 2.5 minutes for 1e16 on one core)"""
import sys

from model import parse
from sim import rl

M = sys.argv[1]
steps = sys.argv[2] if len(sys.argv) > 2 else '1e16'
lines = rl(M, steps, every=0, quiet_f=True)
last = lines[-1].split()
assert last[0] == 'running', lines[-1]           # 'halted N' would mean a halt
f1 = [x for x in lines if x.startswith('F')]      # with quiet_f only entries into F that read a 1 (a halt) are printed
S = [x for x in lines if x.startswith('S')]
st, b0, ms = parse(S[-1])
print(f'{M}: no halt in {int(last[1]):,} steps ({int(last[3]):,} sweeps); F entered {int(last[5]):,} times, never on a 1'
      if not f1 else f'{M}: F READ A 1: {f1[:3]}')
print(f'  last change of shape at step {st:,}: b0 = {b0}, {len(ms)} markers, phases {"".join(p[0] for p, _ in ms)}, '
      f'blocks {[b for _, b in ms]}')
