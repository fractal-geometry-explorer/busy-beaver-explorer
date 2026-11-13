"""Check the tick jumps against the direct simulator: run counters.py to exactly T steps and compare the tape with
tools/c/tmrun.c's at step T.

usage: python3 validate.py MACHINE T [TMRUN]
"""
import os, sys, subprocess, tempfile
from counters import make, HERE

M, T = sys.argv[1], int(float(sys.argv[2]))
tmrun = sys.argv[3] if len(sys.argv) > 3 else None
if tmrun is None:
    tmrun = os.path.join(tempfile.gettempdir(), "bbe_tmrun")
    if not os.path.exists(tmrun):
        subprocess.run(["gcc", "-O2", "-o", tmrun, os.path.join(HERE, "..", "..", "..", "tools", "c", "tmrun.c")], check=True)
c = make(M, log=lambda *a: None)
r = c.run(T, max_direct=10 ** 12, exact=True)
mine = c.tape_str().strip()
out = subprocess.run([tmrun, M, str(T), "every", str(T)], capture_output=True, text=True).stdout.splitlines()[0]
ref = out.split(" ", 1)[1].strip()
print(f"{M}: {T} steps, {c.ticks} ticks jumped, headers {sorted(h for g, h in c.headers)}; tapes equal: {mine == ref}")
sys.exit(0 if mine == ref else 1)
