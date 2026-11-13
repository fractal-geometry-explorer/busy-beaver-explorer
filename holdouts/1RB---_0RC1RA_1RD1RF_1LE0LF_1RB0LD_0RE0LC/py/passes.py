"""The counter passes of 1RB---_0RC1RA_1RD1RF_1LE0LF_1RB0LD_0RE0LC, checked against the C simulator.

Every time the head, in state D, stands on the blank cell just right of the tape, read the tape in two-cell symbols
P = 01 and Q = 11 (aligned to the right end) and group it as P^p Q^q, written p.q.  The right part of the tape is

    ... digit W^n digit W^n ... digit W^n end        W = 2.2 (01011111),  end = 1.0 or 3.0

with the digits  a = 2.5,  b = 2.1,  c = 3.4,  d = 4.3.  Claim checked here, for every pass (one such moment to the
next) and for the digits to the right of the last other group:

  * the end alternates 1.0, 3.0;
  * the lowest digit steps a -> b -> c -> d -> a;
  * a digit steps exactly when the digit to its right made the step d -> a or a -> b (a carry), else it is unchanged;
  * every W run changes its length by at most 1.

usage: python3 passes.py [STEPS]     (default 10^8; prints the counts and the returns to the left end)
"""
import os, re, subprocess, sys
from collections import Counter

M = '1RB---_0RC1RA_1RD1RF_1LE0LF_1RB0LD_0RE0LC'
HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS = os.path.join(HERE, '../../../tools/c')
DIG = {(2, 5): 'a', (2, 1): 'b', (3, 4): 'c', (4, 3): 'd'}
NEXT = {'a': 'b', 'b': 'c', 'c': 'd', 'd': 'a'}
CARRY = {'a', 'd'}          # the digit values whose step sends a carry to the left


def left_cells(line):
    """cells left of the head in a tmrun tape line 'STEP tokens...'"""
    out = []
    for tok in line.split()[1:]:
        m = re.fullmatch(r'(?:([A-F])>)?([01])(?:\^(\d+))?', tok)
        if m.group(1):
            break
        out.append(m.group(2) * int(m.group(3) or 1))
    return ''.join(out)


def tokens(cells):
    """the tape as a list of ('W', n) | (digit, 0) | ('p.q', 0)"""
    if len(cells) % 2:
        cells = '0' + cells
    syms = [cells[i:i + 2] for i in range(0, len(cells), 2)]
    groups, i = [], 0
    while i < len(syms):
        p = q = 0
        while i < len(syms) and syms[i] == '01':
            p += 1; i += 1
        while i < len(syms) and syms[i] == '11':
            q += 1; i += 1
        if p == q == 0:
            groups.append(syms[i]); i += 1
        else:
            groups.append((p, q))
    out = []
    for g in groups:
        if g == (2, 2):
            if out and out[-1][0] == 'W':
                out[-1] = ('W', out[-1][1] + 1)
            else:
                out.append(('W', 1))
        elif g in DIG:
            out.append((DIG[g], 0))
        else:
            out.append((g if isinstance(g, str) else '%d.%d' % g, 0))
    return out


def regular(toks):
    """(end, [(digit, run to its right), ...] from the right) for the part right of the last other group"""
    end = toks[-1][0]
    if end not in ('1.0', '3.0'):
        return None
    i, out = len(toks) - 2, []
    while i >= 0:
        run = 0
        if toks[i][0] == 'W':
            run = toks[i][1]; i -= 1
        if i < 0 or toks[i][0] not in DIG.values():
            break
        out.append((toks[i][0], run)); i -= 1
    return end, out


def main():
    steps = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 8
    exe = os.path.join(HERE, 'tmrun')
    subprocess.run(['gcc', '-O2', '-o', exe, os.path.join(TOOLS, 'tmrun.c')], check=True)
    out = subprocess.run([exe, M, str(steps), 'at', 'D', 'R', '100000000'], capture_output=True, text=True).stdout
    stat, prev, maxd = Counter(), None, 0
    for line in out.splitlines():
        if not line[:1].isdigit():
            continue
        cur = regular(tokens(left_cells(line)))
        stat['passes'] += prev is not None or 0
        if prev and cur and len(prev[1]) >= 1:
            (e0, d0), (e1, d1) = prev, cur
            n = min(len(d0), len(d1))
            if e0 == e1:
                stat['BAD end'] += 1; print('BAD end at', line.split()[0])
            carry, ok, moved = True, True, 0
            for k in range(n):
                (x, r0), (y, r1) = d0[k], d1[k]
                want = NEXT[x] if carry else x
                if y != want or abs(r1 - r0) > 1:
                    ok = False
                moved += carry
                carry = carry and x in CARRY
            if carry and n == len(d0):
                stat['passes whose carry leaves the digits'] += 1
            if len(d0) != len(d1):
                stat['passes that change the number of digits'] += 1
            elif ok:
                stat['passes that follow the digit rule'] += 1
            else:
                stat['BAD digit rule'] += 1; print('BAD digits at', line.split()[0])
            maxd = max(maxd, n)
        elif prev is not None:
            stat['passes with no digit right of the last other group'] += 1
        prev = cur
    for k, v in sorted(stat.items()):
        print('%10d  %s' % (v, k))
    print('most digits in the regular part:', maxd)
    out = subprocess.run([exe, M, str(steps), 'at', 'C', 'L', '1000'], capture_output=True, text=True).stdout
    print('head at the left end in state C at steps:', ' '.join(l.split()[0] for l in out.splitlines() if l[:1].isdigit()))
    return 1 if any(k.startswith('BAD') for k in stat) else 0


if __name__ == '__main__':
    sys.exit(main())
