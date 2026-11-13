"""Reads `tmrun MACHINE STEPS at C L K` output (the tape each time C is at the left end) and writes each tape as a
list of digits: runs of the word b = `1 0^5`, separated by T = `1 0^2 1^5 0^2 (1 0^2)^3` or S = `1 0^2 1^2 0^5`.
Other words: a = `1 0^2`, written aN for N copies; anything else in brackets.

  /home/user/w/tmrun 1RB0LF_1LC1RA_0RD1LB_0LA0RE_1RC1RB_---0LD 10000000000 at C L 1000000 | python3 digits.py
"""
import re, sys
from itertools import groupby

W = {'100': 'a', '100000': 'b', '1100000': 'S', '1111100': 'T', '1100': 'c', '11100': 'd', '1000': 'm', '10000': 'n'}


def expand(rle):
    out = []
    for t in rle.split():
        if '>' in t:
            t = t.split('>')[1]
        if '^' in t:
            s, n = t.split('^')
            out += [s] * int(n)
        else:
            out.append(t)
    return ''.join(out)


def words(s):
    out = [W.get(m.group(), '[' + m.group() + ']') for m in re.finditer(r'1+0*', s.strip('0'))]
    txt = ' '.join(f'{k}{len(list(g))}' for k, g in groupby(out))
    return txt.replace(' a1 T1 a3 ', ' T ').replace(' a1 S1 ', ' S ')


for line in sys.stdin:
    p = line.split(None, 3)
    if len(p) == 4 and p[0].isdigit():
        print(p[0], words(expand(p[3])))
