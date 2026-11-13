"""phases.py [STEPS] : the right-end regime of 1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA--- from blank tape.

Whenever the head reaches a new cell at the right end in state A, check whether the tape is
    (10)^(a+2) 1 (10)^(k_1+2) 1 ... 1 (10)^(k_n+2) (1101010)^(m+1) A>0
which is `T a ks m` of lean/Trip.lean (ks listed from the right, as in Lean). Print one line per run of
consecutive such moments: first and last step, and (a, m, n = number of blocks) at both ends, plus the block
list at the start of the run (abbreviated).
"""
import re, sys

M = "1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---"
T = {}
for i, g in enumerate(M.split('_')):
    for b in range(2):
        x = g[3 * b:3 * b + 3]
        T[(i, b)] = None if x[2] == '-' else (int(x[0]), 1 if x[1] == 'R' else -1, ord(x[2]) - 65)

PAT = re.compile(r'^((?:10){2,})((?:1(?:10){2,})*?)((?:1101010)+)$')


def parse(cells):
    mm = PAT.match(cells)
    if not mm:
        return None
    a = len(mm.group(1)) // 2 - 2
    blocks, s = [], mm.group(2)
    i = 0
    while i < len(s):
        assert s[i] == '1'; i += 1; j = i
        while s[j:j + 2] == '10': j += 2
        blocks.append((j - i) // 2 - 2); i = j
    m = len(mm.group(3)) // 7 - 1
    return a, list(reversed(blocks)), m


def main():
    steps = int(float(sys.argv[1])) if len(sys.argv) > 1 else 3 * 10 ** 7
    tape = bytearray(1 << 21); h = lo = hi = 1 << 20; s = 0
    run = None
    for k in range(1, steps + 1):
        b = tape[h]; tr = T[(s, b)]
        if tr is None:
            print('HALT', k); return
        w, d, s = tr; tape[h] = w; h += d
        if h < lo:
            lo = h
        elif h > hi:
            hi = h
            if s == 0:
                p = parse(''.join('1' if tape[x] else '0' for x in range(lo, hi)).lstrip('0'))
                if p:
                    if run is None:
                        run = [k, p, k, p]
                    else:
                        run[2], run[3] = k, p
                elif run is not None:
                    report(run); run = None
    if run:
        report(run)
    print('no halt in', steps, 'steps')


def report(r):
    (k0, (a0, ks, m0), k1, (a1, ks1, m1)) = r
    ab = ks if len(ks) <= 8 else ks[:4] + ['...'] + ks[-3:]
    print(f"steps {k0:>11,} to {k1:>11,}: a {a0} -> {a1}, m {m0} -> {m1}, {len(ks)} blocks, ks (from the right) {ab}"
          + ("" if ks == ks1 else "  [blocks changed]"))


if __name__ == '__main__':
    main()
