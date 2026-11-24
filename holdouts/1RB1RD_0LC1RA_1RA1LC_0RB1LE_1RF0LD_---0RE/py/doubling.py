"""The doubling form of the phase map (`py/phasemap.py`, `lean/Phases.lean`), and the residue search.

The four machines 1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE, 1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE,
1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE and 1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE share this file; the machine
is the one of `phasemap.py` next to it.  At a left stop E(x, z) (z even) or a right stop R(x, y) / A(x, y) put
s and L as in `SV` below (`sv` of `lean/Doubling.lean`).  Then the next stop has L' = L + 2 and s' = 2s mod L
(`doubling`), except at the low end, at the midpoint 2s = L + MID (`mid_ones`: the all-ones tapes of the fatal
parity) and in the few phases after such an all-ones tape.

usage (from the repository root, with this machine's folder for DIR):
  python3 holdouts/DIR/py/doubling.py check [K]      K phases from blank tape (default 2*10^6): every stop pair, and
                                                     the stops where s' = 2s mod L, L' = L + 2 fails, by kind
  python3 holdouts/DIR/py/doubling.py ones [K]       the all-ones tapes in K phases: length, (s, L) of the stop
                                                     before, and whether the length has the fatal parity
  python3 holdouts/DIR/py/doubling.py relays [N]     the all-ones lengths n < N (default 3*10^5) whose run leads straight
                                                     to another all-ones tape (before any stop), and whether a target
                                                     is fatal
  python3 holdouts/DIR/py/doubling.py residues N...  the residue search: the phase map taken mod N (every branch
                                                     its residues allow), from the start; which all-ones residues
                                                     it reaches, and whether one is a fatal length mod N
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import phasemap  # noqa: E402

M = phasemap.M
RK = phasemap.INIT[0]
# per machine: (s offset of E, L offset of E, s offset of R, L offset of R, parity of y at R stops,
#               MID (the midpoint is 2s = L + MID), length of the all-ones tape it makes = L - OFF, fatal list)
TABLE = {
    "1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE": (1, 7, 5, 8, 1, 1, 5, ((0,), 20, 12)),
    "1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE": (2, 8, 5, 7, 1, 2, 4, ((0, 6), 32, 12)),
    "1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE": (2, 8, 6, 8, 0, 2, 5, ((3,), 28, 13)),
    "1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE": (0, 6, 2, 6, 0, 0, 3, ((1,), 12, 9)),
}
SE, LE, SR, LR, YPAR, MID, OFF, (FEX, FC, FD) = TABLE[M]


def sv(p):
    """(s, L) of a left or right stop."""
    if p[0] == 'e':
        return p[2] + SE, 2 * p[1] + p[2] + LE
    return p[2] + SR, 2 * p[1] + p[2] + LR


def is_stop(p):
    return (p[0] == 'e' and p[2] % 2 == 0 and p[2] >= 2) or (p[0] == RK and p[2] % 2 == YPAR)


def fatal(n):
    if n in FEX:
        return True
    k = 0
    while FC * 2 ** k - 2 * k - FD <= n:
        if FC * 2 ** k - 2 * k - FD == n:
            return True
        k += 1
    return False


def stops(k):
    """The stops (phase index, phase) among the first k phases from blank tape, and every all-ones tape."""
    p = phasemap.INIT
    for i in range(k):
        if p[0] != 'q':
            yield i, p
        r = phasemap.nxt(p)
        if r is None:
            print('HALT at phase', i, p)
            return
        p = r[0]


def regular(a, b):
    (s, L), (s2, L2) = sv(a), sv(b)
    return is_stop(a) and is_stop(b) and L2 == L + 2 and s2 == (2 * s if 2 * s <= L else 2 * s - L)


def check(k):
    prev, n, bad = None, 0, {}
    for i, p in stops(k):
        if prev is not None:
            n += 1
            if not regular(prev[1], p):
                s, L = sv(prev[1])
                if not is_stop(prev[1]):
                    kind = 'after an all-ones tape (off the stops)'
                elif 2 * s == L + MID:
                    kind = 'midpoint 2s = L + %d' % MID
                elif prev[1][0] == 'e' and prev[1][2] == 2:
                    kind = 'low end E(x, 2)'
                elif prev[1][0] == RK and prev[1][1] == 0:
                    kind = 'all-ones stop'
                else:
                    kind = 'other'
                bad.setdefault(kind, []).append((prev[0], prev[1], (s, L), p, sv(p)))
        prev = (i, p)
    print(f'{M}: {n} pairs of consecutive left/right phases in {k} phases')
    print(f'  s\' = 2s mod L, L\' = L + 2 fails at {sum(map(len, bad.values()))} of them:')
    for kind, v in bad.items():
        print(f'  {kind}: {len(v)}, first {v[:2]}')


def ones(k):
    prev = None
    for i, p in stops(k):
        if p[0] == RK and p[1] == 0:
            n = p[2]
            how = ''
            if prev is not None:
                s, L = sv(prev)
                how = f'from {prev}, s = {s}, L = {L}, 2s - L = {2 * s - L}'
            par = 'fatal parity' if n % 2 == (FC * 2 ** 3 - 2 * 3 - FD) % 2 else 'safe parity'
            print(f'n = {n:>12} ({par}{", FATAL" if fatal(n) else ""})  phase {i:>9}  {how}')
        prev = p


def relays(n_max):
    out = []
    for n in range(n_max):
        if fatal(n):
            continue
        p = (RK, 0, n)
        while True:
            p = phasemap.nxt(p)[0]
            if p[0] == 'q':
                continue
            if p[0] == RK and p[1] == 0:
                out.append((n, p[2]))
                break
            if is_stop(p):
                break
    print(f'{len(out)} relays below {n_max}:', ', '.join(f'{a} -> {b}' for a, b in out))
    print('fatal targets:', [b for a, b in out if fatal(b)] or 'none')


def fatal_res(n_mod):
    s = {e % n_mod for e in FEX}
    for k in range(4 * n_mod + 64):
        v = FC * 2 ** k - 2 * k - FD
        if v >= 0:
            s.add(v % n_mod)
    return s


def residues(n_mod, rep=5):
    """Abstract reachability of the phase map mod n_mod.  A class (kind, a mod n, b mod n, ...) stands for all phases
    with those residues; its successors are the classes of the images of the representatives r + n*j, j < rep, of
    every parameter.  With rep = 5 every branch of `nxt` that the residues allow, and both halves of each bounce
    count b (which depends on t mod 2n), is taken, so the reachable classes contain the true orbit."""
    start = (phasemap.INIT[0],) + tuple(v % n_mod for v in phasemap.INIT[1:])
    seen, todo = {start}, [start]
    while todo:
        c = todo.pop()
        for off in itertools.product(range(rep), repeat=len(c) - 1):
            r = phasemap.nxt((c[0],) + tuple(v + n_mod * o for v, o in zip(c[1:], off)))
            if r is None:
                continue
            q = r[0]
            d = (q[0],) + tuple(v % n_mod for v in q[1:])
            if d not in seen:
                seen.add(d)
                todo.append(d)
    ys = {c[2] for c in seen if c[0] == RK and c[1] == 0}
    f = fatal_res(n_mod)
    hit = ys & f
    print(f'mod {n_mod}: {len(seen)} classes reachable, all-ones residues {len(ys)} of {n_mod}, '
          f'fatal residues {len(f)}, in both {len(hit)}' + ('' if hit else '  <-- AVOIDS THE FATAL LIST'))
    return not hit


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'check'
    args = [int(a) for a in sys.argv[2:]]
    if cmd == 'check':
        check(args[0] if args else 2 * 10 ** 6)
    elif cmd == 'ones':
        ones(args[0] if args else 2 * 10 ** 6)
    elif cmd == 'relays':
        relays(args[0] if args else 3 * 10 ** 5)
    elif cmd == 'residues':
        for n_mod in args or range(2, 25):
            residues(n_mod)
