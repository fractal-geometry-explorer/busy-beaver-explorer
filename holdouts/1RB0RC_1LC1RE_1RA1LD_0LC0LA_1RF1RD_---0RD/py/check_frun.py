"""check_frun.py: c/frun.c against the Lean cases one at a time (rules.py's reader of lean/Phases.lean and
lean/Pieces.lean): after each jump of `frun trace N`, the frame, the frame count and the machine step count must be
those of applying the Lean cases one by one from Ph.z 0 0 2 (2 steps).
    gcc -O2 -o frun c/frun.c && ./frun trace 20000 | python3 py/check_frun.py"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rules import lean_next
fr, frames, steps, n = ('z', (0, 0, 2)), 0, 2, 0
for line in sys.stdin:
    if line.startswith("END"): continue
    f, s, t, a, b, c = line.split()
    f, s = int(f), int(s)
    while frames < f:
        fr, k, _ = lean_next(fr)
        assert fr is not None, 'halt'
        frames += 1; steps += k
    want = (t, (int(a), int(b), int(c)))
    if frames != f or fr != want or steps != s:
        print('MISMATCH at jump', n + 1, fr, frames, steps, 'frun:', line.strip()); sys.exit(1)
    n += 1
print('ok: %d jumps, %d frames, %d steps, all agree with the Lean cases' % (n, frames, steps))
