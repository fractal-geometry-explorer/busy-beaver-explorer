"""Read the output of run.py and check the round structure of 1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA.

At every visit of the left end the tape is  1 a^x0 s1 a^x1 s2 ... a^xk  with a = 01 and separators S = 110 and
D = 110110 (D only before the last block).  This script checks, for every round of the run:
  * odd x0: the next first block is (x0 - 3)/2 (so y = x0 + 3 is halved);
  * the machine halts in the round after a visit with x0 = 1 (tested from built tapes by try.py, not here); so it
    halts iff some chain of odd rounds starts at x0 with x0 + 3 a power of two;
and prints, for the chain starts, how far x0 + 3 is from a power of two (the 2-adic valuation against the bit length).

usage: python3 rounds.py rounds.txt
"""
import sys


def load(fn):
    rows = []
    for line in open(fn):
        p = line.split()
        if len(p) < 3 or p[1] != 'E':
            continue
        s = ' '.join(p[3:]).replace('1 1 0 1 1 0', 'D').replace('1 1 0', 'S')
        blocks, seps = [0], []
        for t in s.split():
            if t.startswith('a^') or t == 'a':
                blocks[-1] += int(t[2:]) if t != 'a' else 1
            elif t in 'SD':
                seps.append(t)
                blocks.append(0)
            else:
                blocks = None    # an irregular tape (the first rounds), not of the form above
                break
        if blocks:
            rows.append((int(p[0]), blocks, seps))
    return rows


def v2(n):
    return (n & -n).bit_length() - 1


def even_rule(b, s):
    """The next round after an even first block, or None where it is not known in closed form."""
    x0 = b[0]
    if s == ['D']:
        return [x0 // 2 + 2, x0 + b[1]], ['S']
    if s[0] == 'S' and len(s) > 1:
        nb = [x0 // 2 + b[1] + 2] + b[2:]
        nb[-1] += x0
        return nb, s[1:]
    return None


def main():
    R = load(sys.argv[1])
    bad = 0
    starts = []
    prev_even = True
    for i in range(len(R) - 1):
        x, y = R[i][1][0], R[i + 1][1][0]
        if x % 2:
            if y != (x - 3) // 2:
                bad += 1
                print('odd round off the rule:', R[i])
            if prev_even:
                starts.append(x)
        prev_even = x % 2 == 0
    from collections import Counter
    ev = Counter()
    for (t, b, s), (t2, b2, s2) in zip(R, R[1:]):
        if b[0] % 2 == 0:
            p = even_rule(b, s)
            if p is None:
                ev['S, two blocks: tape becomes one block a^L, then ' + ('ok' if s2 == ['D'] and b2[1] == 2 * b2[0] + 2 else 'OTHER')] += 1
            else:
                ev['rule ok' if p == (b2, s2) else 'rule FAILS'] += 1
    print('even rounds:', dict(ev))
    print(f'rounds {len(R)}, odd rounds off the rule {bad}, chains of odd rounds {len(starts)}')
    print('x0 = 1 never seen' if all(r[1][0] != 1 for r in R) else 'x0 = 1 SEEN')
    top = sorted(((v2(s + 3), s.bit_length(), s) for s in starts), reverse=True)[:8]
    print('longest chains (v2(x0+3), bits of x0+3): ', [(a, b) for a, b, _ in top])
    print('closest approach (bits - v2):', min(b - a for a, b, _ in ((v2(s + 3), (s + 3).bit_length(), s) for s in starts)))
    print('first block at the end has', R[-1][1][0].bit_length(), 'bits; step count', len(str(R[-1][0])), 'digits')


if __name__ == '__main__':
    main()
