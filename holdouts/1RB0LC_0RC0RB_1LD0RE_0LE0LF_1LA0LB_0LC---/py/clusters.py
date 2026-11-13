"""Where the machine could halt: random small tapes of the family's shape, run until a halt or a step limit.

The tapes are 1 (0010)^b0 m1 (0010)^b1 ... mk (0010)^bk 000 with 1 to 4 random markers and short random blocks (0 to 6
words), the head in state E on the blank cell after them (first group's orientation; the second group runs the
mirror image, head in state C).  Many of them halt within a few thousand steps, while the merges of markers with long
blocks around them do not halt (merges.py): a halt needs short blocks close together.  usage: python3 clusters.py MACHINE [TRIES [SEED]]
"""
import random
import sys

from family import mirrored

WORD = {'0': '1', "0'": '0', '1': '0011', '2': '011', '3': '11', '4': '00111'}


def table(M):
    t = {}
    for i, tr in enumerate(M.split('_')):
        for s in (0, 1):
            x = tr[3 * s:3 * s + 3]
            t[(i, s)] = None if x[2] == '-' else (int(x[0]), 1 if x[1] == 'R' else -1, ord(x[2]) - 65)
    return t


def run(M, cells, limit):
    """The machine on `cells` (left to right), head on the blank cell after them in the sweep-end state."""
    t = table(M)
    if mirrored(M):
        tape = {len(cells) - i: v for i, v in enumerate(cells)}   # mirror image: the cells to the right, reversed
        h, st = 0, 2                                       # core state E is C in the mirror
    else:
        tape = {i - len(cells): v for i, v in enumerate(cells)}
        h, st = 0, 4
    for n in range(limit):
        tr = t[(st, tape.get(h, 0))]
        if tr is None:
            return n + 1
        w, d, st2 = tr
        tape[h] = w
        h += d
        st = st2
    return None


def main(M, tries=2000, seed=1):
    rnd = random.Random(seed)
    halts = []
    for _ in range(tries):
        b0 = rnd.choice([0, 1, 2, 3, 5])
        ms = [(rnd.choice(list(WORD)), rnd.choice([0, 0, 1, 1, 2, 3, 6])) for _ in range(rnd.randint(1, 4))]
        s = '1' + '0010' * b0 + ''.join(WORD[p] + '0010' * b for p, b in ms) + '000'
        r = run(M, [int(c) for c in s], 20000)
        if r:
            halts.append((r, b0, ms))
    return halts


if __name__ == '__main__':
    M = sys.argv[1]
    tries = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
    h = main(M, tries, int(sys.argv[3]) if len(sys.argv) > 3 else 1)
    print(f'{M}: {len(h)} of {tries} random short tapes halt within 20,000 steps')
    for r, b0, ms in sorted(h)[:5]:
        print(f'  halts after {r} steps: b0 = {b0}, markers {ms}')
