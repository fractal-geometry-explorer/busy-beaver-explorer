"""The block rules of 1RB---_1LC0LC_1RD1LB_1LE1RD_0LA1LF_1LD0RF against the real run (c/stats.c).

usage: python3 stats.py [STEPS] [FROM]      (defaults 2e10 and 0; about 80 s)

Prints, for the steps from FROM on: the parity of the head's cell for every (state, symbol); the passes to the
right by the rule that applies (the length of the next block); the gaps met with B on the leftmost 1 of a block
(four 0s would be the halt); and how close the head came to the right end of the tape in every octave of steps.
"""
import os, subprocess, sys, tempfile

M = '1RB---_1LC0LC_1RD1LB_1LE1RD_0LA1LF_1LD0RF'
HERE = os.path.dirname(os.path.abspath(__file__))

if __name__ == '__main__':
    steps = int(float(sys.argv[1])) if len(sys.argv) > 1 else 20_000_000_000
    frm = int(float(sys.argv[2])) if len(sys.argv) > 2 else 0
    exe = os.path.join(tempfile.gettempdir(), 'stats_130302')
    subprocess.run(['gcc', '-O2', '-o', exe, os.path.join(HERE, '../c/stats.c')], check=True)
    subprocess.run([exe, M, str(steps), str(frm)], check=True)
