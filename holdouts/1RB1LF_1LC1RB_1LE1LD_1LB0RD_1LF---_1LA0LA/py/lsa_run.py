"""Jump from a wall visit straight to the next right-end event:  python3 lsa_run.py <1|2> <e> [explicit] [file]

1 = 1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA, 2 = 1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA.
The macro simulator with the digit engine (msim.py, geng.py) runs from blank tape to the first wall visit past
10^e; from the word there the level-stripping accelerator (lsa_*.py) finds the visit of the next right-end event:
the ladder is a mixed-radix counter (lsa_ladder, lsa_region), and an eater's K super-cycles are jumped at once
(lsa_eater: the super-cycle law, derived with the fuel symbolic; lsa_phase: the hits above a run of K blocks in
closed form, counts too large to write down are kept as BigF: a mantissa and an exact exponent).  Prints the phases met and
the event's visit: exact, or as that closed form.  'explicit' turns the phase jumps off (only batches of hits:
the same answer, slower, for a cross-check).  'file': save the starting word (pickle) or read it if it exists.
LSA_CKPT=file: checkpoint every LSA_EVERY phases and resume from it; LSA_LOG=file: log every phase (for lsa_laws.py).
"""
import sys, os, time, threading, pickle
sys.set_int_max_str_digits(0)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import msim, geng
from msim import Macro
import lsa_phase
from lsa_phase import PRegion, run_to_event
MS = {'1': "1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA", '2': "1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA"}


def num(n):
    s = str(n); return s if len(s) <= 24 else "%s..(%d digits)" % (s[:12], len(s))


def start_word(which, e):
    """the word right of the wall at the first landing of the outer wall past visit 10^e (no event pending)"""
    mm = Macro(MS[which]); mm.topcap = 10 ** 100
    out = {}
    def trace(m, mv, toks, T2):
        if m.landed:
            if mv < m.topcap:
                m.topcap = 10 ** 100
                return
            if m.topv >= 10 ** e and mv >= 10 ** 50 and not out:
                out.update(visit=m.topv, steps=m.steps, toks=geng.to_tokens(T2))
            m.topcap = min(m.topcap * m.topcap, 10 ** max(e, 100))
    mm.trace = trace
    while not out:
        if mm.run(max_msteps=mm.msteps + 2000) == 'halt':
            raise SystemExit("HALT at step %d" % mm.steps)
    return out


def main():
    which, e = sys.argv[1], int(sys.argv[2])
    args = sys.argv[3:]
    if 'bigf' in args:            # test: keep only small numbers exact
        lsa_phase.EXACT_BITS = 1000
        args.remove('bigf')
    if 'explicit' in args:
        lsa_phase.KMIN = 10 ** 30
        args.remove('explicit')
    t0 = time.time()
    if args and os.path.exists(args[0]):
        d = pickle.load(open(args[0], 'rb'))
    else:
        d = start_word(which, e)
        if args:
            pickle.dump(d, open(args[0], 'wb'))
    print("start: wall visit %s, step %s, %d tokens (%.1fs)" % (num(d['visit']), num(d['steps']), len(d['toks']),
                                                               time.time() - t0), flush=True)
    R = PRegion(d['toks'], op='G', Q=int(os.environ.get('LSA_Q', '200')))
    print("%d levels on top of a bottom word" % len(R.levels), flush=True)
    lg = os.environ.get('LSA_LOG')
    if lg:
        # one record per phase, appended: (phase, eater tokens with the fuel, fuel index, first 120 tokens of the
        # rest, K, P, fuel per super-cycle, hits down, block multiplier); read by the twin's py/lsa_laws.py
        logf = open(lg, 'ab')
        from lsa_region import prefix_tokens

        def hook(nph, sc, E, fi, rest, K):
            a = lsa_phase.block_map_c(sc, E)[1]
            pickle.dump((nph, list(E), fi, prefix_tokens(rest, 120)[0], K, sc['P'], sc['dm'], sc['c'], a), logf)
            logf.flush()
        lsa_phase.HOOK[0] = hook
    ck = os.environ.get('LSA_CKPT')
    if ck and os.path.exists(ck):
        R, frames, nph = lsa_phase.load_state(ck)
        print("resumed from %s at phase %d" % (ck, nph), flush=True)
    else:
        frames, nph = None, 0
    z = run_to_event(R, ckpt=ck, every=int(os.environ.get('LSA_EVERY', '200')), frames=frames, nph=nph)
    if isinstance(z, lsa_phase.BigF):
        z = z.add(d['visit'] - 1)
        print("next right-end event at wall visit about 2^%d (%.15g * 2^%d), about 10^%.12g;  %d phases" % (
            z.E, z.m, z.E, z.log10(), len(lsa_phase.FRAMES)))
        pickle.dump([(f[0], f[2], f[3], f[4], f[5]) for f in lsa_phase.FRAMES],   # (used, P, a, b, K) per phase
                    open('lsa_frames_%s.pkl' % which, 'wb'))
    else:
        print("exact: visit %d   (the next visit is the event)" % (d['visit'] + z - 1))
    print("%.1fs" % (time.time() - t0))


threading.stack_size(1024 << 20)
th = threading.Thread(target=main); th.start(); th.join()
