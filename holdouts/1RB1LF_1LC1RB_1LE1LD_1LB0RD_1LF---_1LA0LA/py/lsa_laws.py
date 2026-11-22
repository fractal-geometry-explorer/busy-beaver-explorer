"""The laws between consecutive eater phases, from a phase log:  python3 lsa_laws.py LOG [LOG...] [--ckpt CK...]

LOG: records written by `LSA_LOG=LOG python3 lsa_run.py ...` (one pickle per phase: phase number, eater tokens
with the fuel, fuel index, first tokens of the rest, K, P, fuel per super-cycle dm, hits down c, and the block
multiplier a; logs without a are read too).  For each pair of consecutive phases of the x64 kind (dm = 4, c = 21)
the next fuel F' is classified against K, the super-cycles of the phase before:

    law A   11 F' = 21 K + e   (a fresh fuel, one rung for every 11 hits passed down)
    law B   F' = K + delta     (a fresh fuel, one rung for every 21 hits)
    list    anything else: the next fuel is an older run of the word (the eater has used up its fresh fuel)

and the ranges of e, delta and the slack F - 4K are printed: they are the constants of lean/Descent.lean of
1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA.  With the block multipliers it also prints sum K log2(a), a lower
bound for log2 of the top hits needed to get past the logged phases (Descent.phases_compose, Descent.blk_ge).
--ckpt: the bottom word of checkpoints (lsa_phase.save_state): how many long runs it holds, and their digits.
"""
import sys, pickle, math, os
from collections import Counter
sys.set_int_max_str_digits(0)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def read_log(paths):
    rows = {}
    for fn in paths:
        with open(fn, 'rb') as f:
            while True:
                try:
                    d = pickle.load(f)
                except EOFError:
                    break
                rows[d[0]] = d          # a phase logged twice (after a resume) is the same phase
    return [rows[k] for k in sorted(rows)]


def laws(R):
    st = Counter(); ex = {'A': [], 'B': [], 'slack': []}
    for r, s in zip(R, R[1:]):
        if s[0] != r[0] + 1:
            st['gap in the log'] += 1
            continue
        F = r[1][r[2]][1]; K = r[4]; dm, c = r[6], r[7]
        F2 = s[1][s[2]][1]
        if (dm, c) != (4, 21):
            st['other kind (P, dm, c) = %s' % ((r[5], dm, c),)] += 1
            continue
        ex['slack'].append(F - 4 * K)
        e = 11 * F2 - 21 * K; d = F2 - K
        if 0 <= d <= 12:
            st['B'] += 1; ex['B'].append(d)
        elif -1000 < e < 1000:
            st['A'] += 1; ex['A'].append(e)
        else:
            st['list'] += 1
    return st, ex


def ckpt_stats(path):
    st = pickle.load(open(path, 'rb'))
    B = st['B']
    big = [t for t in B if type(t) is tuple and t[0] == 'P' and t[1] > 1000]
    fu = [t for t in big if t[2] == (1, 0, 0)]
    return st['nph'], len(B), len(big), sum(len(str(t[1])) for t in big), len(fu)


def main():
    args = sys.argv[1:]
    cks = []
    if '--ckpt' in args:
        i = args.index('--ckpt'); cks = args[i + 1:]; args = args[:i]
    if args:
        R = read_log(args)
        print('%d phases logged (%d to %d)' % (len(R), R[0][0], R[-1][0]))
        st, ex = laws(R)
        for k, v in sorted(st.items(), key=lambda x: -x[1]):
            print('  %-40s %d' % (k, v))
        for k in ('A', 'B', 'slack'):
            v = ex[k]
            if v:
                print('  %-6s from %d to %d; most common %s' % (k, min(v), max(v), Counter(v).most_common(4)))
        if all(len(r) > 8 for r in R):
            tot = sum(r[4] * (r[8].bit_length() - 1) for r in R if r[8] > 1)
            print('sum K log2(a) = %.6e: the logged phases need at least 2^that top hits (10^%.6e)' % (
                tot, tot * math.log10(2)))
    for ck in cks:
        nph, nt, nb, dig, nf = ckpt_stats(ck)
        print('%s: after phase %d the bottom word has %d tokens, %d runs longer than 1000 (%d digits in all), '
              '%d of them fuels (1 0 0)^F' % (ck, nph, nt, nb, dig, nf))


if __name__ == '__main__':
    main()
