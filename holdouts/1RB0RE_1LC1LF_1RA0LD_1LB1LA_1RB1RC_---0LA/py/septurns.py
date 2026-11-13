"""Log the head turns of 1RB0RE_1LC1LF_1RA0LD_1LB1LA_1RB1RC_---0LA at the separators of its block list.

Reads the output of `hturn MACHINE STEPS H` (one line per turn: step, side, state, extent, distance, tape with `>`)
and cuts the tape into blocks of the word 110.  For each turn it prints the step, the side (R = the head turned
after going right, L = after going left), the state, the index of the block boundary where the head turned
(counted from the left end), and the lengths of the blocks on each side of it, together with the separator text
between them.

usage: hturn M STEPS 6 | python3 septurns.py
"""
import re
import sys

for line in sys.stdin:
    f = line.split()
    if len(f) < 6:
        continue
    step, side, st, tape = f[0], f[1], f[2], f[5]
    h = tape.index('>')
    t = tape.replace('>', '')
    blocks = [(m.start(), m.end()) for m in re.finditer(r'(?:110)+', t)]
    # the boundary at the head: the last block ending at or before h, and the next block
    i = max([k for k, (a, b) in enumerate(blocks) if b <= h + 1] or [-1])
    left = (blocks[i][1] - blocks[i][0]) // 3 if i >= 0 else 0
    right = (blocks[i + 1][1] - blocks[i + 1][0]) // 3 if i + 1 < len(blocks) else 0
    sep = t[blocks[i][1] if i >= 0 else 0:blocks[i + 1][0] if i + 1 < len(blocks) else len(t)]
    off = h - (blocks[i][1] if i >= 0 else 0)
    print(step, side, st, i + 1, len(blocks), left, sep[:12], right, off)
