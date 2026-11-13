"""The trains of 1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB.

Reads the output of `c/snapR.c` (the tape from the first 1 to the head, each time the head makes a new right record
in state C) and prints, whenever the list of trains changes other than in the nearest one, every train: a stretch of
the second sea `1110 1110 ...` (at least two words), as `position:words`, the position counted from the left end of
the tape, nearest train (to the head) first.

usage: gcc -O2 -o snapR c/snapR.c && ./snapR MACHINE 3000000 1 C > s.txt && python3 py/trains.py s.txt
"""
import re
import sys

TRAIN = re.compile(r'(?:1110){2,}|(?:0111){2,}|(?:1011){2,}|(?:1101){2,}')


def trains(s):
    """(position from the left end, number of words), nearest the head (the right end) first."""
    return [(m.start(), len(m.group(0)) // 4) for m in TRAIN.finditer(s)][::-1]


def main(path):
    prev = None
    for line in open(path):
        n, p, s = line.split()
        t = trains(s)
        key = [k for _, k in t]
        if prev is None or len(prev) != len(key) or prev[1:] != key[1:]:
            print(n, len(s), ' '.join('%d:%d' % x for x in t))
        prev = key


if __name__ == '__main__':
    main(sys.argv[1])
