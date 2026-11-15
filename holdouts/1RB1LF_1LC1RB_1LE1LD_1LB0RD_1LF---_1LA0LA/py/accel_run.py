"""Accelerated exact run of the twins from blank tape:  python3 accel_run.py <1|2> <seconds> [cap exponent [events]]

1 = 1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA, 2 = 1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA.
The macro simulator (msim.py, cells) runs the machine; whenever the head stands at a wall in front of a word of the
pairs X = 10, Y = 11 it hands the wall visits to the digit engine (geng.py).  Prints one line per jump of the outer
wall, the right-end events (EVENT: the visit that follows reaches the blank right end; the simulator does it on
cells), and HALT if the machine halts.  The first jump is capped at 10^cap visits (default 100), then the cap is
squared after every full jump and reset at an event.
"""
import sys, time, threading
sys.set_int_max_str_digits(0)
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import msim, geng
from msim import Macro
from geng import show, to_tokens
MS = {'1': "1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA", '2': "1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA"}
MM = [None]
EV = [0]


def num(n):
    s = str(n)
    return s if len(s) <= 24 else "%s...(%d digits)" % (s[:12], len(s))


def summ(T):
    toks = to_tokens(T)
    big = [t[1] for t in toks if type(t) is tuple and t[0] == 'R' and t[1] > 50]
    return "%d tokens, %d levels (10)^n with n > 50" % (len(toks), len(big))


def main():
    M = MS[sys.argv[1]]
    secs = float(sys.argv[2])
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else 100
    mm = Macro(M)
    MM[0] = mm
    mm.topcap = 10 ** cap
    t0 = time.time()

    def trace(m, mv, toks, T2):
        if m.landed:
            print("[%.1fs] +%s wall visits -> visit %s, step %s; %s" % (time.time() - t0, num(mv), num(m.topv),
                                                                      num(m.steps), summ(T2)))
            if mv < m.topcap:
                print("   EVENT at the next visit; word: %s" % show(T2, 45)[:700])
                print("   exact: visit %d step %d" % (m.topv, m.steps))
                EV[0] += 1
                m.topcap = 10 ** cap
            elif m.topcap < 10 ** 20000:
                m.topcap = m.topcap * m.topcap
            sys.stdout.flush()
    mm.trace = trace
    nev = int(sys.argv[4]) if len(sys.argv) > 4 else None       # stop when this many events have been reached
    while time.time() - t0 < secs and (nev is None or EV[0] < nev):
        try:
            r = mm.run(max_msteps=mm.msteps + 2000)
        except (RecursionError, MemoryError):
            print("the engine ran out of recursion depth or memory (a nested structure it has no rule for)")
            geng.STACK.clear()
            break
        if r == 'halt':
            print("HALT: step %s, state %s, wall visits so far %s" % (num(mm.steps), "ABCDEF"[mm.s], num(mm.topv)))
            break
    print("end: wall visit %s, step %s, %d hooks (%d from event plans), %d macro steps, %.1fs; engine %s" % (
        num(mm.topv), num(mm.steps), mm.hooks, mm.planned, mm.msteps, time.time() - t0, geng.STATS))


def status():
    while True:
        time.sleep(60)
        mm = MM[0]
        if mm is not None:
            print("  .. %d hooks, %d macro steps, left runs %d, engine depth %d" % (mm.hooks, mm.msteps, len(mm.L),
                                                                                 len(geng.STACK)))
            sys.stdout.flush()


threading.Thread(target=status, daemon=True).start()
threading.stack_size(1 << 30)
th = threading.Thread(target=main)
th.start()
th.join()
