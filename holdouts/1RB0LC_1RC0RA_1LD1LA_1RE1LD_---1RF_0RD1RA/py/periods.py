"""Times between the right-end records of a run, and how they double.

usage: tmrun M N records 100000 > rec.txt;  python3 periods.py rec.txt STATE [K]

Takes the records (new cell on the right) whose head is in STATE, and prints for the last K of them: the step, the
steps d since the previous such record, and d - 2*d_prev (the correction to exact doubling).  Shared by the three
"digit list with binary clock" machines of batch 4 (1RB0LC_1RC0RA_..., 1RB---_1RC1RF_..., 1RB---_1RC0LF_...).
"""
import sys


def main(path, state, k):
    ts = []
    for line in open(path):
        p = line.split(' ', 3)
        if len(p) == 4 and p[1] == 'R' and (state + '>') in p[3]:
            ts.append(int(p[0]))
    prev_d = None
    rows = []
    for a, b in zip(ts, ts[1:]):
        d = b - a
        rows.append((b, d, None if prev_d is None else d - 2 * prev_d))
        prev_d = d
    for b, d, c in rows[-k:]:
        print(b, d, '' if c is None else c)


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 40)
