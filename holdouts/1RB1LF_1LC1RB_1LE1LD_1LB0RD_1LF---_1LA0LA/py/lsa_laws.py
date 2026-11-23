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
--ckpt: the bottom word of checkpoints (lsa_phase.save_state): how many long runs it holds, and their digits (pieces
of one periodic run, stored as several tokens, are counted as one run).
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


def groups(B, thr=1000):
    """the long runs of a bottom word B, with neighbouring runs merged when they are one periodic run: the engine
    often stores one run of the rung as many P tokens in different rotations, with the junction digits between
    them.  Returns [index, count, pieces, word]."""
    from lsa_phase import _tok_digits
    idx = [i for i, t in enumerate(B) if type(t) is tuple and t[0] == 'P' and t[1] > thr]
    G = []; cur = None
    for a, b in zip([None] + idx, idx):
        T = B[b]; same = False
        if a is not None and cur is not None and len(T[2]) == len(B[a][2]):
            mid = []; ok = True
            for t in B[a + 1:b]:
                dd = _tok_digits(t)
                if dd is None or len(mid) + len(dd) > 2000:
                    ok = False; break
                mid += dd
            if ok:
                L = len(T[2]); s = list(B[a][2]) * 2 + mid + list(T[2]) * 2
                same = all(s[i] == s[i - L] for i in range(L, len(s)))
                if same:
                    cur[1] += T[1] + len(mid) // L; cur[2] += 1
        if not same:
            cur = [b, T[1], 1, T[2]]; G.append(cur)
    return G


def ckpt_stats(path):
    st = pickle.load(open(path, 'rb'))
    B = st['B']
    big = [t for t in B if type(t) is tuple and t[0] == 'P' and t[1] > 1000]
    G = groups(B)
    fu = [g for g in G if g[3] == (1, 0, 0)]
    return st['nph'], len(B), len(big), len(G), sum(len(str(g[1])) for g in G), len(fu)


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
        nph, nt, nb, ng, dig, nf = ckpt_stats(ck)
        print('%s: after phase %d the bottom word has %d tokens and %d P tokens longer than 1000, which are %d runs '
              '(%d digits in all), %d of them fuels (1 0 0)^F' % (ck, nph, nt, nb, ng, dig, nf))


if __name__ == '__main__':
    main()
