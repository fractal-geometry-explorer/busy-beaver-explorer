"""What the tail of the counter sees.  At the 'o o' records of a phase the tape is

    0^inf B> 0  (D0, o) (0, o) (Y, x)  T          (blocks (D, x) = (10)^D x, as in recp / blockmm)

with D0 the countdown block and Y the growing block.  T is the tail.  Between two such records (one increment)
T changes in a way that depends only on Y mod 2 and x, not on D0: four operators

    E0: Y even, x = o      E1: Y odd, x = i      O0: Y odd, x = o      O1: Y even, x = i

each computed by a direct run of the machine on a constructed tape (D0 = 61, Y = 20 or 21) until T first changes.
This script checks, on a recp file (direct simulation; first argument):
  1. the operators do not depend on D0 or on the size of Y (D0 in 41, 61, 81 and Y in 20/21, 30/31, at every
     PROBE-th 'o o' record);
  2. inside every phase, the tail goes through E0, E1, E0, E1, ... (Y + x is even at every 'o o' record);
  3. across each reset, the word of operators of length <= 6 that takes the last tail before the reset to the
     tail one increment after the first 'o o' record of the new phase (the shortest one, found by search; the
     first increment of a phase, with Y = 1, is not counted in 2.).
usage: python3 tail_ops.py RECP_FILE [PROBE] [MAXREC]"""
import sys, itertools

W = [[1, 0], [0, 0], [0, 1], [1, 0], [0, 1], [1, 0]]
MV = [[1, -1], [-1, 1], [1, -1], [-1, -1], [1, 1], [-1, 0]]
NX = [[1, 5], [2, 4], [0, 3], [1, 3], [0, 2], [0, -1]]


def enc(blocks):
    out = []
    for D, x in blocks:
        out += [1, 0] * D + [x]
    return out


def parse_cells(cells):
    bl, k, n = [], 0, len(cells)
    while k < n:
        D = 0
        while k + 1 < n and cells[k] == 1 and cells[k + 1] == 0:
            D += 1; k += 2
        if k < n:
            bl.append((D, cells[k])); k += 1
        elif D:
            bl.append((D, 0))
    while bl and bl[-1] == (0, 0):
        bl.pop()
    return bl


def next_record(c, blocks, maxsteps=10 ** 8):
    """0^inf B> c enc(blocks) 0^inf -> the next left record (c', blocks', steps), or ('HALT', steps)."""
    t = bytearray([0] * 4 + [c] + enc(blocks) + [0] * 64); h = 4; s = 1; lo = h; st = 0
    while st < maxsteps:
        if h < 0:
            t = bytearray(1000) + t; h += 1000; lo += 1000
        if h >= len(t):
            t += bytearray(1000)
        x = t[h]
        if s == 5 and x == 1:
            return ('HALT', st)
        if s == 1 and h < lo:
            return (t[h], parse_cells(list(t[h + 1:])), st)
        t[h] = W[s][x]; d = MV[s][x]; s = NX[s][x]; h += d; st += 1
    return ('LONG', st)


OPS = {'E0': (0, 0), 'E1': (1, 1), 'O0': (1, 0), 'O1': (0, 1)}


def apply(op, T, D0=61, Y0=20):
    py, x = OPS[op]
    Y = Y0 + ((Y0 + py) % 2)
    c, bl = 0, [(D0, 0), (0, 0), (Y, x)] + list(T)
    for _ in range(40):
        r = next_record(c, bl, 10 ** 6)
        if r[0] in ('HALT', 'LONG'):
            return r[0]
        c, bl, _ = r
        if len(bl) >= 3 and bl[1] == (0, 0) and bl[3:] != list(T):
            return tuple(bl[3:])
    return 'SAME'


def parse(line):
    head, _, rest = line.partition('|')
    f = head.split(); toks = rest.split(); bl = []; i = 0
    while i < len(toks):
        t = toks[i]
        if t.isdigit():
            if i + 1 < len(toks) and toks[i + 1] in 'io':
                bl.append((int(t), 1 if toks[i + 1] == 'i' else 0)); i += 2
            else:
                bl.append((int(t), 0)); i += 1
        else:
            bl.append((0, 1 if t == 'i' else 0)); i += 1
    return int(f[0]), int(f[1]), int(f[3]), bl


def main():
    fn = sys.argv[1]
    probe = int(sys.argv[2]) if len(sys.argv) > 2 else 500
    maxrec = int(float(sys.argv[3])) if len(sys.argv) > 3 else 10 ** 9
    oo = []          # (record, D0, Y, x, tail) at the 'o o' records
    for line in open(fn):
        if '|' not in line:
            continue
        st, rec, hc, bl = parse(line)
        if rec > maxrec:
            break
        if hc == 0 and len(bl) > 3 and bl[1] == (0, 0) and bl[0][1] == 0 and bl[0][0] >= 1:
            oo.append((rec, bl[0][0], bl[2][0], bl[2][1], tuple(bl[3:])))
    print('%d o-o records' % len(oo))
    # 1. independence
    bad = 0
    for k in range(0, len(oo), probe):
        T = oo[k][4]
        for op in OPS:
            ref = apply(op, T)
            for D0 in (41, 81):
                bad += apply(op, T, D0=D0) != ref
            bad += apply(op, T, Y0=30) != ref
    print('1. operators independent of D0 and Y size at %d probes: %s' % ((len(oo) + probe - 1) // probe,
                                                                         'yes' if not bad else 'NO (%d)' % bad))
    # 2. and 3.
    inside = ok = 0; resets = []
    nxt = {oo[k][0]: oo[k + 1] for k in range(len(oo) - 1)}
    for a, b in zip(oo, oo[1:]):
        if b[0] - a[0] == 2 and b[1] == a[1] - 2 and b[2] >= 4:
            inside += 1
            op = 'E0' if (a[2] % 2, a[3]) == (0, 0) else ('E1' if (a[2] % 2, a[3]) == (1, 1) else None)
            ok += op is not None and apply(op, a[4]) == b[4]
        else:
            if b[0] in nxt:
                resets.append((a, nxt[b[0]]))
    print('2. increments inside phases: %d, of which E0/E1 as predicted: %d' % (inside, ok))
    memo = {}

    def ap(op, T):
        if (op, T) not in memo:
            memo[op, T] = apply(op, T)
        return memo[op, T]
    for a, b in resets:
        found = None
        for n in range(1, 7):
            for w in itertools.product(OPS, repeat=n):
                T = a[4]
                for op in w:
                    T = ap(op, T)
                    if isinstance(T, str):
                        break
                if T == b[4]:
                    found = w; break
            if found:
                break
        print('3. reset, records %d to %d (countdown %d -> %d, Y %d%s -> %d%s): tail word %s' % (
            a[0], b[0], a[1], b[1], a[2], 'oi'[a[3]], b[2], 'oi'[b[3]], ' '.join(found) if found else 'none <= 6'))


if __name__ == '__main__':
    main()
