"""Iterate the class-round map of ctxmulti.py (folder of 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---) for
1RB0RA_0RC0LB_1LD1RF_1LE1RA_1RD1RB_1LA--- far beyond the direct run, with a checkpoint after every round
(trust level: computation; each round is an extrapolation from small instances, as in ctxmulti.py).

usage: python3 ctxorbit.py CHECKPOINT.pkl ROUNDS     (resumes from the checkpoint if it exists; TCELLS as in ctxmulti)
Prints one line per round (modulus Q, number of tokens, bits of the largest count, cumulative simulations, time)
followed by the token list.  Round 0 is the last event of the direct run to 3e9 steps (after checking the 17 rounds
of the direct run against the class map).
"""
import os, sys, time, pickle
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', '1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---', 'py'))
import ctxmulti as CM

M = '1RB0RA_0RC0LB_1LD1RF_1LE1RA_1RD1RB_1LA---'


def main():
    ck, rounds = sys.argv[1], int(sys.argv[2])
    mu = CM.Multi(M, 'L', 'B', '0', tcells=int(os.environ.get('TCELLS', '40')))
    if os.path.exists(ck):
        st = pickle.load(open(ck, 'rb')); toks, done = st['toks'], st['done']
    else:
        r = CM.check(mu, '3e9'); print('check', r[:4], flush=True)
        toks, done = r[4][1], 0
    while done < rounds:
        t0 = time.time(); o = mu.rnd(toks)
        if o[0] != 'ok':
            print('STOP at round', done, o, flush=True); print(CM.show(toks, 5000)); break
        toks = o[1]; done += 1
        print('round', done, 'Q', o[2], 'tokens', len(toks), 'largest', max(c for _, c in toks).bit_length(), 'bits',
              'sims', mu.eng.nsim, '%.1fs' % (time.time() - t0), flush=True)
        print('  ', CM.show(toks, 3000), flush=True)
        pickle.dump({'toks': toks, 'done': done}, open(ck + '.tmp', 'wb')); os.replace(ck + '.tmp', ck)


if __name__ == '__main__':
    main()
