"""How close the model orbit comes to the one halting equation of coq/SOC23Match.v, for
1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB--- and 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1RC---.

halts_iff_r5_match (Coq) says: the machine halts iff, at some rule R5 (a shifted counter cfgS1 with an
odd number h = 2a+1 of digits running out), the unread rest m of the right counter satisfies
    m + 1 = (2D+1) * 2^s,   s = 3a+3,   D = 2^len - 1 - k (how far the left counter is below full).
This script iterates the round map of SOC23Model.v from (L, X) = (2, 5) in the deficit form of
c/model23.c (a round starts with D = 0, a countdown of n adds n, an overflow that appends s digits
sends D to (2D+1)*2^s) and, at every R5 end, compares m + 1 with the target T = (2D+1)*2^s:
  - lowmatch: the low s bits of m are 1s and bit s is 0 (m + 1 and T agree on their low s+1 bits);
  - dbits:    how many further bits agree, i.e. how many low bits of 2D+1 the rest of m+1 matches;
  - shorter:  rounds where T has more bits than m + 1 (the lengths cross, so size alone cannot exclude T).

usage: python3 r5_match.py ROUNDS
"""
import sys
sys.set_int_max_str_digits(0)


def split(m):
    """m = (x*2+1)*2^i -> (x, i), m > 0."""
    i = (m & -m).bit_length() - 1
    return m >> (i + 1), i


def round_map(L, X):
    """One round from cfgL L 0 X. Returns (L', X', end, info); info = (T, m+1, s) at R5."""
    m, h = split(X)
    S1, nodd, D, ln = False, 0, 0, L
    while True:
        D += (2 ** h - 1) * 2 + nodd                     # the countdown of the shifted counter
        a = h // 2
        if not S1:
            if h % 2 == 0:                               # R1
                s = 3 * a
                if m == 0:
                    ln += 1 + s
                    return ln, 2 ** ln - (2 * D + 1) * 2 ** s + 1, 'R1', None
                D = (2 * D + 1) * 2 ** s; ln += 1 + s
                m, h = split(m); S1, nodd = True, 0
            else:                                        # R2
                s = 3 * a + 2
                if m == 0:
                    ln += 1 + s
                    return ln, 2 ** ln - (2 * D + 1) * 2 ** s, 'R2', None
                D = (2 * D + 1) * 2 ** s; ln += 1 + s
                m, h = split(m); S1, nodd = False, 1
        else:
            if h % 2 == 0:
                if m == 0:                               # R3, blank
                    s = 3 * a + 2; ln += 1 + s
                    return ln, 2 ** ln - (2 * D + 1) * 2 ** s, 'R3', None
                if m % 2 == 0:                           # R3
                    s = 3 * a + 2
                    D = (2 * D + 1) * 2 ** s; ln += 1 + s
                    m, h = split(m // 2); S1, nodd = True, 1
                else:                                    # R4
                    s = 3 * a + 1
                    D = (2 * D + 1) * 2 ** s; ln += 1 + s
                    m, h = split(m + 1); S1, nodd = False, 0
            else:                                        # R5: the round ends, m is left unread
                s = 3 * a + 3
                T = (2 * D + 1) * 2 ** s
                ln += 1 + s
                return ln, 2 ** ln - T + m + 1, 'R5', (T, m + 1, s)


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    L, X = 2, 5
    ends = {}
    r5 = low = 0
    best = (0, None, None)
    shorter = []
    for t in range(N):
        if X == 2 ** L:
            print('corner at round', t); return
        L, X, end, info = round_map(L, X)
        ends[end] = ends.get(end, 0) + 1
        if info is None:
            continue
        r5 += 1
        T, M, s = info
        if M == T:
            print('R5 match (corner) at round', t); return
        x = M ^ T
        agree = (x & -x).bit_length() - 1                # low bits on which M and T agree
        if T.bit_length() > M.bit_length():
            shorter.append(t)
        if agree > s:
            low += 1
            if agree - s > best[0]:
                best = (agree - s, t, (2 * (T >> s)).bit_length() - 1)
    print(f'{N} rounds from (2, 5), no corner; ends: {ends}; final L = {L}')
    print(f'R5 ends: {r5}; low s bits of m all 1 and bit s 0: {low}')
    print(f'most bits of 2D+1 matched after that: {best[0]} (round {best[1]}, 2D+1 has {best[2]} bits)')
    print(f'rounds where (2D+1)*2^s is longer than m+1: {len(shorter)} {shorter[:20]}')


if __name__ == '__main__':
    main()
