"""Log the context of every right-end event met by the accelerated run (msim + geng), for the event-to-event study.

usage: python3 evlog.py <1|2> <seconds> <halting-hits file> [cap exponent]
For every visit batch that ends in an event (the outer events and every event inside the return sweeps), prints:
the depth of nested sub-visit frames, the kind of leaf, the innermost event word (a, b) (the two-digit word whose
visit reaches the blank right end), the innermost frames (k = digit of the frame, done = its sub-visits finished),
and, when the innermost frame's hit word (k T) is at most 18 pairs long, whether that hit is in the list of
halting hits (direct simulation, events.py).
"""
import sys, os, time, threading
sys.set_int_max_str_digits(0)
sys.setrecursionlimit(30000000)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import msim, geng
from msim import Macro
MS = {'1': "1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA", '2': "1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA"}
HALT = set()
LOG = []


def digits(T, n):
    out = []
    try:
        while T is not None and len(out) < n:
            t = T[0]
            if type(t) is tuple:
                if t[0] == 'Z': out += [0] * min(t[1], n)
                elif t[0] == 'R': out += [1, 0] * min(t[1], n)
                elif t[0] == 'P': out += list(t[2]) * min(t[1], n)
                elif t[0] == 'E': T = t[1]; continue
                else: out.append('?')
            else: out.append(t)
            T = T[1]
    except Exception:
        out.append('?')
    return out[:n], T is None and len(out) <= n


def wrap(M, toks):
    T2, done = geng.gpow(M, toks)
    if done is not True:
        tr = list(geng.EVTRACE)
        if tr:
            W = tr[0][2]
        else:
            W = T2
        wd, wfull = digits(W, 4)
        frames = [(conc(k), d) for S, d, Wf, c, k in tr[:6]]
        hit = None
        if tr:
            S, d, Wf, c, k = tr[0]
            sd, sfull = digits(S, 19)
            if sfull and sd and sd[0] != '?' and sd[0] >= 2:
                hw = (conc(k), sd[0] - 2) + tuple(sd[1:])
                if sum(hw) + len(hw) <= 18:
                    hit = (hw, hw in HALT)
        hws = []
        for S, d, Wf, c, k in tr[:4]:      # the hit words (k, S - 2) of the innermost frames, when short
            sd, sfull = digits(S, 120)
            if sfull and sd and '?' not in sd and sd[0] >= 2:
                hws.append((conc(k),) + (sd[0] - 2,) + tuple(sd[1:]))
            else:
                break
        key = (len(tr), geng.EVLEAF[0], tuple(wd), tuple(frames))
        if LOG and LOG[-1][0] == key:
            LOG[-1][1] += 1
            return T2, done
        LOG.append([key, 1])
        print("EV depth %d leaf %s word %s frames(k,done) %s hit %s hitwords %s" % (
            len(tr), geng.EVLEAF[0], tuple(wd) if wfull else tuple(wd) + ('...',), frames, hit,
            " | ".join(" ".join(map(str, w)) for w in hws)), flush=True)
    return T2, done


def conc(x):
    return x if type(x) is int else getattr(x, 'v', x)


def main():
    M = MS[sys.argv[1]]
    secs = float(sys.argv[2])
    for line in open(sys.argv[3]):
        if line.strip():
            HALT.add(tuple(map(int, line.split())))
    msim.gpow = wrap
    mm = Macro(M)
    cap = int(sys.argv[4]) if len(sys.argv) > 4 else 100
    mm.topcap = 10 ** cap
    t0 = time.time()

    def trace(m, mv, toks, T2):
        # as accel_run.py: the cap on a jump of the outer wall is squared after every full jump, reset at an event
        if m.landed:
            if mv < m.topcap:
                print("OUTER EVENT at wall visit %d digits, step %d digits" % (len(str(m.topv)), len(str(m.steps))),
                      flush=True)
                m.topcap = 10 ** cap
            elif m.topcap < 10 ** 20000:
                m.topcap = min(m.topcap * m.topcap, 10 ** 20000)
    mm.trace = trace
    while time.time() - t0 < secs:
        r = mm.run(max_msteps=mm.msteps + 2000)
        if r == 'halt':
            print("HALT", flush=True)
            break
    print("end: wall visit %s digits, step %s digits, %d events logged, %.0fs" % (
        len(str(mm.topv)), len(str(mm.steps)), len(LOG), time.time() - t0), flush=True)


if os.environ.get("FAULTDUMP"):
    import faulthandler
    faulthandler.dump_traceback_later(int(os.environ["FAULTDUMP"]), repeat=True)
threading.stack_size(int(os.environ.get("STACKMB", "1024")) << 20)
th = threading.Thread(target=main)
th.start()
th.join()
