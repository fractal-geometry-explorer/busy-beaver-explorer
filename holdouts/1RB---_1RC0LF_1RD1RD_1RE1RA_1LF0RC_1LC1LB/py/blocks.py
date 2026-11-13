"""The macro configuration of 1RB---_1RC0LF_1RD1RD_1RE1RA_1LF0RC_1LC1LB at the right end of the tape.

usage: tmrun M 1e11 records 100000 > rec.txt;  python3 blocks.py rec.txt [K]

At each record (new cell) on the right in state E, tests whether the tape is  1^(3a) 0 (1^(3m+2) 0)* E>0  (a run of
1s of length divisible by 3, then blocks of 2 mod 3 ones each followed by one 0), counts the records that are and
are not, and prints the last K regular ones as: step, steps since the previous E record, a, the list of m.
"""
import re
import sys


def expand(t):
    cells = []
    for tok in t.split():
        if '>' in tok:
            tok = tok[2:]
        if '^' in tok:
            c, n = tok.split('^')
            cells += [int(c)] * int(n)
        else:
            cells.append(int(tok))
    return ''.join(map(str, cells))


def main(path, k):
    ok = bad = 0
    rows, prev = [], 0
    for line in open(path):
        p = line.split(' ', 3)
        if len(p) < 4 or p[1] != 'R' or ' E>' not in ' ' + p[3]:
            continue
        s, tape = int(p[0]), expand(p[3])
        if re.fullmatch(r'(111)*0(11(111)*0)*', tape):
            ok += 1
            a = tape.index('0') // 3
            ms = [(len(x) - 2) // 3 for x in re.findall('1+', tape[tape.index('0'):])]
            rows.append((s, s - prev, a, ms))
        else:
            bad += 1
        prev = s
    print('regular', ok, 'irregular', bad)
    for s, d, a, ms in rows[-k:]:
        print(s, d, a, ' '.join(map(str, ms)))


if __name__ == '__main__':
    main(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 10)
