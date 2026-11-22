"""Jump from a wall visit straight to the next right-end event:  python3 lsa_run.py <1|2> <e> [explicit] [file]

1 = 1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA, 2 = 1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA.
The macro simulator with the digit engine (msim.py, geng.py) runs from blank tape to the first wall visit past
10^e; from the word there the level-stripping accelerator (lsa_*.py) finds the visit of the next right-end event:
the ladder is a mixed-radix counter (lsa_ladder, lsa_region), and an eater's K super-cycles are jumped at once
(lsa_eater: the super-cycle law, derived with the fuel symbolic; lsa_phase: the hits above a run of K blocks in
closed form, lsa_sym: numbers sum c_i 2^(e_i) for the ones too large to write down).  Prints the phases met and
the event's visit: exact, or as that closed form.  'explicit' turns the phase jumps off (only batches of hits:
the same answer, slower, for a cross-check).  'file': save the starting word (pickle) or read it if it exists.
"""
import sys, os, time, threading, pickle
sys.set_int_max_str_digits(0)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import msim, geng
from msim import Macro
import lsa_phase
from lsa_phase import PRegion, run_to_event
from lsa_sym import Sym
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
    R = PRegion(d['toks'], op='G')
    print("%d levels on top of a bottom word" % len(R.levels), flush=True)
    z = run_to_event(R)
    if isinstance(z, Sym):
        print("next right-end event at wall visit  %d + (%s)  ~ 10^(%.10g)" % (d['visit'], z, z.log10()))
        print("closed form (all terms):")
        for ex, c in sorted(z.t.items(), reverse=True):
            print("   %s * 2^%d" % (c, ex))
    else:
        print("exact: visit %d   (the next visit is the event)" % (d['visit'] + z - 1))
    print("%.1fs" % (time.time() - t0))


threading.stack_size(1024 << 20)
th = threading.Thread(target=main); th.start(); th.join()
