"""The four regimes of 1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC and the concrete closure test.

usage: python3 regimes.py phases            print every phase of the four regimes (one round trip each)
       python3 regimes.py closure [BB]       from each regime, first count a in [6, 6+3p), b = BB + 0/1/2: run until
                                             a regime is reached again (default BB 3000)

A left-end tape `B> 00 (01)^a 000 (01)^b ...` is written as a list ['00', a, '000', b, ...]: numbers are counts of
`01`, strings literal cells.  Runs use the C simulator c/simfrom.c (compiled on first use into /tmp).
"""
import os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
M = "1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC"
SIM = "/tmp/simfrom_36670"

# one representative of each regime (phase 0), found along the run from blank tape, and its period in round trips
REG = {
    'R0': ['00', 481, '000', 415, '000', 10, '000', 10, '000', 7, '000', 6, '11000', 2],
    'R1': ['00', 5422, '000', 1213, '000', 10, '000', 22, '000', 13, '00001000', 4, '000', 4, '000', 6, '11000', 2],
    'R2': ['00', 5875, '000', 301, '000', 10, '000', 43, '00001000', 7, '000', 10, '00001000', 2],
    'R3': ['00', 5977, '000', 196, '000', 10, '000', 25, '000', 18, '11', 6, '000', 2]}
P = {'R0': 15, 'R1': 22, 'R2': 16, 'R3': 9}


def sim():
    if not os.path.exists(SIM):
        subprocess.run(['gcc', '-O2', '-o', SIM, os.path.join(HERE, '..', 'c', 'simfrom.c')], check=True)
    return SIM


def parse(s):
    out, i, lit = [], 0, ''
    while i < len(s):
        n = 0
        while s.startswith('01', i + 2 * n):
            n += 1
        if n >= 2:
            if lit:
                out.append(lit)
                lit = ''
            out.append(n)
            i += 2 * n
        else:
            lit += s[i]
            i += 1
    if lit:
        out.append(lit)
    return out


def unparse(l):
    return ''.join('01' * x if isinstance(x, int) else x for x in l)


def left_turns(l, maxsteps=10 ** 10):
    """Run from `B> unparse(l)` and yield the list at each later left-end visit of B (or 'HALT')."""
    p = subprocess.Popen([sim(), M, unparse(l), '0', 'B', str(maxsteps), 'B', 'L'], stdout=subprocess.PIPE, text=True)
    try:
        for line in p.stdout:
            if line.startswith('HALT'):
                yield 'HALT'
                return
            if line[0] in 'EO':
                return
            yield parse(line.split()[3])
    finally:
        p.kill()


def phases(name):
    out = [REG[name]]
    for l in left_turns(REG[name]):
        out.append(l)
        if len(out) > P[name]:
            break
    return out


def phase_index():
    idx = {}
    for r in REG:
        for i, l in enumerate(phases(r)[:-1]):
            idx[(l[2], tuple(map(str, l[4:])))] = (r, i)
    return idx


def reach(start, idx, minA, maxrounds=100000):
    """Run until the list is a regime phase with first count >= minA: ('OK', (regime, phase), a, b, rounds)."""
    for k, l in enumerate(left_turns(start)):
        if l == 'HALT':
            return ('HALT', k)
        if len(l) >= 4 and l[0] == '00' and isinstance(l[1], int) and isinstance(l[3], int) and l[1] >= minA:
            m = idx.get((l[2], tuple(map(str, l[4:]))))
            if m:
                return ('OK', m, l[1], l[3], k + 1)
        if k > maxrounds:
            break
    return ('NONE', None)


def main():
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'phases'
    if cmd == 'phases':
        for r in REG:
            ph = phases(r)
            assert ph[-1][4:] == ph[0][4:]
            for i, l in enumerate(ph[:-1]):
                print(r, i, l)
            print(r, 'per period: a %+d, b %+d' % (ph[-1][1] - ph[0][1], ph[-1][3] - ph[0][3]))
    elif cmd == 'closure':
        BB = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
        idx = phase_index()
        for r in REG:
            for a in range(6, 6 + 3 * P[r]):
                for rb in range(3):
                    l = list(REG[r])
                    l[1], l[3] = a, BB + rb
                    print(r, 'a=%d b=%d ->' % (a, BB + rb), reach(l, idx, BB // 2), flush=True)


if __name__ == '__main__':
    main()
