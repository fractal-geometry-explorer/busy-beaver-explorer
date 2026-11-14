"""The twin 1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC--- has the round words of the Z system on its tape.

usage: twinchk.py STEPS FILE   (FILE written by zeval.py)
Runs the twin from blank tape and, at every new leftmost cell entered in state E, looks for a round word S_k of
FILE (longer than 20 cells) in the tape.  Prints one line per such visit: index, tape length, [(k, offset)].
At every second visit the tape is 0 0 0 1 0 S_k.
"""
import sys
TWIN = "1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---"
tm = {}
for qi, q in enumerate(TWIN.split('_')):
    for c in (0, 1):
        t = q[3 * c:3 * c + 3]
        tm[(qi, c)] = None if t[0] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, 'ABCDEF'.index(t[2]))
N = int(sys.argv[1])
ref = [l.split()[1] for l in open(sys.argv[2])]
tape = {}; pos = 0; st = 0; lo = hi = 0; n = 0; i = 0
while n < N:
    c = tape.get(pos, 0)
    if pos < lo and st == 4:
        s = ''.join(str(tape.get(j, 0)) for j in range(pos, hi + 1)).rstrip('0')
        print(i, len(s), [(k + 1, s.find(r)) for k, r in enumerate(ref) if len(r) > 20 and r in s]); i += 1
    lo = min(lo, pos); hi = max(hi, pos)
    t = tm[(st, c)]
    if t is None:
        print('HALT'); break
    tape[pos] = t[0]; pos += t[1]; st = t[2]; n += 1
