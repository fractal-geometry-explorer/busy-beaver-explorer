"""The base-4 counter of 1RB---_1RC1RF_1LD1RA_1LB0LE_1LF1LF_0RB0LD, checked against the C simulator.

Read the tape as the gaps between consecutive 1s (the number of 0s between them).  Every time the head, in state D,
is at the left end, the gap list is

    2^n0  d1  2^n1  d2  2^n2 ...  dk  2^nk  END

blocks of gap 2 (the period-3 background 001001...) separated by defects d_i, one of
    q = (1,0)   r = (4)   s = (1,1)   p = (3)
and END = (1) followed by the last 1.  One round (from one such moment to the next) adds 1 to a base-4 counter
whose digits are the defects, least significant first, with q -> r -> s -> p -> q, a carry on s -> p; n0 grows
by 1, and when a digit goes q -> r the block after it loses one period.

usage: python3 counter.py [STEPS]   (default 1e8)
Prints how many rounds the rule predicts exactly, and the rounds it does not cover, by kind:
  overflow   the carry reaches the end of the tape (END, or a defect touching it),
  collision  the carry reaches a compound defect (two defects with no block between them), or a q with an empty
             block after it.
When a block is used up the rule predicts the compound (the two defects written next to each other).
A round the rule covers but predicts wrongly is an error (there are none).
"""
import os, subprocess, sys, collections, tempfile

M = '1RB---_1RC1RF_1LD1RA_1LB0LE_1LF1LF_0RB0LD'
HERE = os.path.dirname(os.path.abspath(__file__))
DIG = {'1 0': 'q', '4': 'r', '1 1': 's', '3': 'p'}
NEXT = {'q': 'r', 'r': 's', 's': 'p', 'p': 'q'}


def parse(line):
    """'STEP D: tokens | t' -> (step, [n0, c1, n1, ..., ck, nk, endcluster]) with clusters as strings."""
    st, rest = line.split(' D: ')
    body, end = rest.split(' | ')
    out, cur, n = [], [], 0
    started = False
    for t in body.split():
        g, _, c = t.partition('^')
        c = int(c) if c else 1
        if g == '2':
            if cur or not started:
                if started:
                    out.append(' '.join(cur))
                cur = []
                out.append(c)
            else:
                out[-1] += c
            started = True
        else:
            if not started:
                out.append(0); started = True
            cur += [g] * c
    out.append(' '.join(cur) + ' |' + end.strip())
    return int(st), out


def predict(x):
    """The rule's next list, or (kind, None) when the round is not covered."""
    if len(x) < 3 or any(not isinstance(x[i], int) for i in range(0, len(x) - 1, 2)):
        return 'shape', None
    y = list(x)
    y[0] += 1
    i = 1
    while True:
        if i >= len(y) - 1:
            return 'overflow', None
        if y[i] not in DIG:
            return 'collision', None
        d = DIG[y[i]]
        if d == 'q':
            if y[i + 1] == 0:
                return 'collision', None
            y[i + 1] -= 1
        y[i] = {v: k for k, v in DIG.items()}[NEXT[d]]
        if d != 's':
            if y[i + 1] == 0:  # the block is used up: the two defects now touch (a compound defect)
                y[i:i + 3] = [y[i] + ' ' + y[i + 2]]
            return 'ok', y
        i += 2


def main(steps):
    exe = os.path.join(tempfile.gettempdir(), 'gaps83770')
    subprocess.run(['gcc', '-O2', '-o', exe, os.path.join(HERE, '../c/gaps.c')], check=True)
    p = subprocess.Popen([exe, M, str(int(steps)), 'D', 'L'], stdout=subprocess.PIPE, text=True)
    prev = None
    stats = collections.Counter()
    maxdig = 0
    for line in p.stdout:
        if line.startswith('halted'):
            print('HALTED', line); return 1
        cur = parse(line)
        if prev is not None:
            kind, y = predict(prev[1])
            if kind == 'ok':
                stats['ok' if y == cur[1] else 'ERROR'] += 1
                if y != cur[1]:
                    print('mismatch at', cur[0], prev[1][:12], cur[1][:12])
            else:
                stats[kind] += 1
        maxdig = max(maxdig, (len(cur[1]) - 2) // 2)
        prev = cur
    total = sum(stats.values())
    print(f'{total + 1} left-end visits in {int(steps):,} steps; rounds predicted exactly: {stats["ok"]}; '
          f'not covered: overflow {stats["overflow"]}, collision {stats["collision"]}, end {stats["end"]}, '
          f'shape {stats["shape"]}; wrong predictions: {stats["ERROR"]}; most digits: {maxdig}')
    return 1 if stats['ERROR'] else 0


if __name__ == '__main__':
    sys.exit(main(float(sys.argv[1]) if len(sys.argv) > 1 else 1e8))
