"""The ladder below the factory, and how the factory refuels:  python3 lsa_refuel.py [N]

The word below the eater of 1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA (after phase 999 of the run from wall
visit 10^3200, checkpoint of lsa_run.py) reads: the factory (see lsa_factory.py) with its fuel [100]^M, then a
*ladder* of five blocks (10)^R0 ... (10)^R4 (R0 = 10^143.5, each about a quarter of the one before) whose
junctions hold the 0^7 / 0^4 3 / 3 0^2 3 digits of a counter, then the next fuel [100]^(10^146.5).  WORD below is
that stretch, with R0..R4 and M as parameters.  Two rules, checked here on N random values (default 20):

* counting: the 2 hits the factory passes on for every 11 it gets are counted by the ladder in base 4.  After 11 q
  hits to the factory (M large) block i has grown by q / 4^i, up to the carries of the counter (|error| <= 1);
* refuelling: when [100]^M is used up, a few hits turn the top block (10)^R0 into the next fuel
      [100]^(2 floor((R0 - 1) / 3) - 4)
  and the ladder moves up by one block: the new blocks are R'_j = R_(j+1) + (R0 / 3) / 4^(j+1), up to the
  carries (|error| <= 3); the fuel after the ladder gains at most one unit.
So the factory never stops: each time its fuel runs out it burns the top block of the ladder, which it has been
counting up itself (one unit for every 11 hits).
"""
import sys, os, random
sys.set_int_max_str_digits(0)
sys.setrecursionlimit(1000000)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import geng
import lsa_phase  # noqa: F401  (sets the step constants of the engine)

WORD = [4, 3, ('R', 1), 4, ('Z', 1), 3, ('Z', 3), ('R', 1), 4, ('Z', 6), ('R', 1), 4, ('Z', 4), 3, 'M', ('Z', 1), 3, 3,
        'R0', ('Z', 7), 'R1', ('Z', 7), ('R', 2), 4, ('P', 2, (1, 0, 0)), ('Z', 3), 4, ('Z', 3), 'R2', ('Z', 7), 'R3',
        3, ('Z', 5), ('R', 2), 4, ('R', 1), ('Z', 1), 3, ('R', 2), 4, 3, ('R', 1), 4, ('Z', 1), 3, ('Z', 3), ('R', 2),
        4, 3, 4, ('Z', 3), ('R', 2), ('P', 1, (4, 3)), 4, 3, ('R', 1), 4, ('R', 1), ('Z', 4), 4, ('R', 1), ('Z', 2), 3,
        ('Z', 3), 4, ('R', 1), ('Z', 2), 3, ('Z', 3), ('R', 1), 4, ('Z', 1), 3, ('Z', 3), 'R4', ('Z', 5), 3, 'M2',
        ('Z', 1)]
# what follows the next fuel: the start of the next ladder (its blocks, 10^146 and less, set to 10^12)
TAIL = [3, ('Z', 3), ('R', 1000000000000), 3, ('Z', 5), ('R', 1), 4, ('Z', 3), 4, ('P', 2, (1, 0, 0)), ('Z', 3), ('R', 2), 4, 3, ('R', 1), 4, ('Z', 1), 3, ('Z', 3), ('R', 1000000000000), ('Z', 4), 3, ('R', 1000000000000), 3, ('Z', 5), ('R', 1), 4, ('Z', 3), 4, ('P', 2, (1, 0, 0)), ('Z', 3), ('R', 2), 4, 3, ('R', 1), 4, ('Z', 1), 3, ('Z', 3), ('R', 1000000000000), ('Z', 7), ('R', 1000000000000), ('Z', 4), 3, ('R', 1), 4, ('Z', 3), 4, ('P', 2, (1, 0, 0)), ('Z', 3), ('R', 2), 4, 3, ('R', 1), 4, ('Z', 1), 3, ('Z', 3), ('R', 1000000000000), 3, ('Z', 5), ('R', 1000000000000), ('Z', 7), ('R', 1), 4, ('Z', 3), 4, ('P', 2, (1, 0, 0)), ('Z', 3), ('R', 2), 4, 3, ('R', 1), 4, ('Z', 1), 3, ('Z', 3), ('R', 1000000000000), ('Z', 4)]
M2 = 10 ** 12


def word(M, R):
    out = []
    for t in WORD:
        if t == 'M':
            out.append(('P', M, (1, 0, 0)))
        elif t == 'M2':
            out.append(('P', M2, (1, 0, 0)))
        elif type(t) is str:
            out.append(('R', R[int(t[1])]))
        else:
            out.append(t)
    return out + list(TAIL)


def after(M, R, q):
    W, done = geng.hpow(q, geng.build(word(M, R), (('O', 0), None)))
    return [t for t in geng.to_tokens(W) if type(t) is tuple and t[0] in 'PR' and t[1] > 5]


def ladder(rng):
    R = [rng.randint(3000, 30000)]
    for i in range(4):
        R.append(R[-1] // 4 + rng.randint(-3, 3))
    return R


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    rng = random.Random(1)
    worst_c = worst_r = 0
    for it in range(N):
        R = ladder(rng)
        q = rng.choice([44, 176, 704, 2816])
        big = after(10 ** 9, R, 11 * q)
        Rn = [t[1] for t in big if t[0] == 'R'][:5]
        err = max(abs((Rn[i] - R[i]) - q / 4 ** i) for i in range(5))
        worst_c = max(worst_c, err)
        assert err <= 1, (R, q, Rn)
        big = after(24, R, 77)
        P = big[0]
        assert P[0] == 'P' and P[2] == (1, 0, 0), big[:3]
        assert P[1] == 2 * ((R[0] - 1) // 3) - 4, (R, P)
        Rn = [t[1] for t in big[1:5]]
        assert [t[0] for t in big[1:5]] == ['R'] * 4 and big[5][2] == (1, 0, 0) and big[5][1] - M2 in (0, 1), big[:6]
        err = max(abs(Rn[j] - R[j + 1] - R[0] / 3 / 4 ** (j + 1)) for j in range(4))
        worst_r = max(worst_r, err)
        assert err <= 3, (R, Rn)
        print('R = %s:  after %5d hits block growth ok;  refuel: [100]^%d, ladder %s' % (R, 11 * q, P[1], Rn))
    print('%d ladders: counting holds (worst carry error %.2f), refuelling holds (worst %.2f)' % (N, worst_c, worst_r))


if __name__ == '__main__':
    main()
