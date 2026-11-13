"""Views of the run of 1RB---_0RC0LA_1LD0RB_1LE0RF_1LF1LC_1LB0LD used in the README, from the C simulator.

usage: python3 view.py [STEPS] [EVERY] [blocks|gaps] [STATE] [L|R] [PERIOD]
  blocks: the tape each time the head, in STATE ('*' any), is at the left (L) or right (R) end of the visited part,
          with runs of words of up to PERIOD cells compressed as (w)^n (c/blocks.c);
  gaps:   the same moments, the tape as the list of gaps between consecutive 1s, run-length coded (c/gaps.c).
EVERY: print every EVERY-th such moment.  Defaults: ['2e9', 200, 'blocks', 'F', 'L', 12].
"""
import os, subprocess, sys, tempfile

M = '1RB---_0RC0LA_1LD0RB_1LE0RF_1LF1LC_1LB0LD'
DEF = ['2e9', 200, 'blocks', 'F', 'L', 12]
HERE = os.path.dirname(os.path.abspath(__file__))


def main(argv):
    a = list(argv) + DEF[len(argv):]
    steps, every, kind, state, side, period = a
    src = os.path.join(HERE, '../c', kind + '.c')
    exe = os.path.join(tempfile.gettempdir(), kind + '_' + M[:20])
    subprocess.run(['gcc', '-O2', '-o', exe, src], check=True)
    args = [exe, M, str(int(float(steps))), state, side]
    args += [str(period), str(every)] if kind == 'blocks' else [str(every)]
    subprocess.run(args, check=True)


if __name__ == '__main__':
    main(sys.argv[1:])
