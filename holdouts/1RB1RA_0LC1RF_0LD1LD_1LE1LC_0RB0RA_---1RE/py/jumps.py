"""The jumps of 1RB1RA_0LC1RF_0LD1LD_1LE1LC_0RB0RA_---1RE, the only places where the block-list run can halt.

A refuel leaves  ... u x 2 z0  (front first; the new carry 2 next to the fuel z0, even).  The carry drains x, z pays 2
a visit.  If x <= z0/2 the carry eats x and moves on (no jump).  If x >= z0/2 + 1 the fuel runs out first: the carry
is still next to z when z = 0, it becomes the new z = 2 z0 + 4 (even), and x is left with the remnant

    r = x - z0/2 - 1.

The target is then the last even block before z: r itself if r is even (it drains u; r = 0 and u = 0 halts), otherwise
the head skips r and the odd blocks before it, and the machine halts iff r = 1, or a skipped block is 1, or no even
block is left.  So a halt at a jump needs an exact coincidence of three block lengths, e.g. x = z0/2 + 2 for r = 1.

This script runs fastrun.py's exact accelerated run and prints, for each jump, the visit, the sizes (bits) of the
fuel F = z0/2 + 1 and the remnant r, r mod 8, and the length and minimum of the skipped stretch, then a summary.

usage: python3 jumps.py DIGITS SECONDS     (run to 10^DIGITS steps or until SECONDS have passed)
"""
import sys, time
import fastrun
from fastrun import RLE

LOG = []
_pop = RLE._pop


def pop(s):
    r = s.r
    i = len(r) - 2
    c = r[i][0]
    if c % 2 == 0 and i >= 1:
        # the carry (even, after its decrement) is next to z = 0: a jump; r[i-1] is the remnant
        rem = r[i - 1][0]
        F = (c - 2) // 4            # c = 2 + 4F
        j = i - 1
        while j >= 0 and r[j][0] % 2 == 1:
            j -= 1
        skipped = sum(cnt for _, cnt in r[j + 1:i])
        mn = min((x for x, _ in r[j + 1:i]), default=None)
        LOG.append((s.v, F, rem, skipped, mn, r[j][0] if j >= 0 else None))
    return _pop(s)


RLE._pop = pop


def main():
    digits, secs = int(sys.argv[1]), float(sys.argv[2])
    g = RLE([1], steps=1, visits=1)
    t0 = time.time(); nxt = 10
    try:
        while nxt <= 10 ** digits and time.time() - t0 < secs:
            g.run(maxsteps=nxt)
            nxt *= 10 if nxt < 10 ** 100 else 10 ** 20
    except fastrun.Halt as h:
        print('HALT', h)
    print('run to ~10^%d steps (~2^%d visits): %d jumps' % (len(str(g.steps)) - 1, g.v.bit_length(), len(LOG)))
    print(' visit(bits) F(bits) r(bits) r%8 skipped min_skipped target')
    for v, F, rem, sk, mn, tg in LOG:
        sz = lambda x: x if x is None or x < 10 ** 6 else '2^%d' % x.bit_length()
        print('  %4d %4d %4d %d %s %s %s' % (v.bit_length(), F.bit_length(), rem.bit_length(), rem % 8, sz(sk), sz(mn), sz(tg)))
    rems = [rem for _, _, rem, _, _, _ in LOG]
    print('smallest remnant r: %d; smallest log2(r/F): %.1f; sum over jumps of 1/r: %.3g' % (
        min(rems), min(rem.bit_length() - F.bit_length() for _, F, rem, _, _, _ in LOG), sum(1 / rem for rem in rems)))
    print('smallest skipped block: %s' % min(mn for *_, mn, _ in LOG if mn is not None))


if __name__ == '__main__':
    main()
