"""Print the drain phases of the exact accelerated run (py/accel.py): each time the final block (9-cell word) is
drained 11 words per period, the step, the final block's length Y, the tape length W (cells), and the delta pattern.

usage (from the repo root): python3 holdouts/1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---/py/rounds.py MACHINE MAXSTEPS
(set ACCEL_X=1 for 1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---)
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import accel  # noqa: E402


def main():
    M = sys.argv[1]
    mx = int(float(sys.argv[2]))
    S = accel.Sim(M)
    pend = {}

    def oj(rule, k):
        d = rule[2]
        if -11 not in d:
            return
        rs = accel.reps(S.c)
        i = d.index(-11)
        y = rs[i].n + k * 11          # before the jump
        w = sum(len(z.w) * z.n for z in rs) - k * sum(len(z.w) * x for z, x in zip(rs, d))
        print('%.6e Y=%d W=%d pattern=%s' % (S.c.steps, y, w, [x for x in d if x]), flush=True)
    S.on_jump = oj
    try:
        S.run(mx)
    except accel.Halted as h:
        print('HALT', h)
    print('end %.6e' % S.c.steps)


if __name__ == '__main__':
    main()
