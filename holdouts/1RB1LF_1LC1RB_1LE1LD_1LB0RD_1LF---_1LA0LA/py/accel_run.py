"""Accelerated exact run of the twins from blank tape:  python3 accel_run.py <1|2> <seconds> [cap exponent [events [max cap exponent]]]

1 = 1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA, 2 = 1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA.
The macro simulator (msim.py, cells) runs the machine; whenever the head stands at a wall in front of a word of the
pairs X = 10, Y = 11 it hands the wall visits to the digit engine (geng.py).  Prints one line per jump of the outer
wall, the right-end events (EVENT: the visit that follows reaches the blank right end; the simulator does it on
cells), and HALT if the machine halts.  The first jump is capped at 10^cap visits (default 100), then the cap is
squared after every full jump (up to 10^(max cap exponent), default 10^20000; a jump of 10^x visits recurses
about 3.3 x levels deep) and reset at an event.
"""
import sys, os, time, threading
sys.set_int_max_str_digits(0)
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import msim, geng
from msim import Macro
from geng import show, to_tokens
MS = {'1': "1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA", '2': "1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA"}
MM = [None]
CAPMAX = [10 ** int(sys.argv[5]) if len(sys.argv) > 5 else 10 ** 20000]   # largest jump of the outer wall
EV = [0]
HK = []
TM = [False]


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
        if os.environ.get('TMALLOC') and not TM[0] and len(str(m.topv)) >= int(os.environ['TMALLOC']):
            import tracemalloc
            tracemalloc.start(3); TM[0] = True
            print("     tracemalloc started", flush=True)
        HK.append((len(str(getattr(m, 'last_call', (0,))[0])), len(str(mv)), round(time.time() - t0, 1), m.planned))
        del HK[:-20]
        if m.landed:
            print("[%.1fs] +%s wall visits -> visit %s, step %s; %s" % (time.time() - t0, num(mv), num(m.topv),
                                                                      num(m.steps), summ(T2)))
            if mv < m.topcap:
                print("   EVENT at the next visit; word: %s" % show(T2, 45)[:700])
                print("   exact: visit %d step %d" % (m.topv, m.steps))
                EV[0] += 1
                m.topcap = 10 ** cap
            elif m.topcap < CAPMAX[0]:
                m.topcap = min(m.topcap * m.topcap, CAPMAX[0])
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
            if os.environ.get('HOOKLOG'):
                print("     stats", {k: v for k, v in geng.STATS.items()}, "last hooks (digits of M, digits of m, "
                      "time, planned):", HK[-6:])
                L = mm.L
                print("     left runs nearest the head (block as %d cells, count):" % mm.K,
                      [(format(b, mm.fmt), c) for b, c in L[-14:]][::-1])
                import collections
                cc = collections.Counter(format(b, mm.fmt) for b, c in L)
                print("     distinct blocks among left runs: %d; commonest:" % len(cc), cc.most_common(6))
            if os.environ.get('MEMLOG') and len(geng.STACK) > 3000:
                import gc
                def rss():
                    return int(open('/proc/self/statm').read().split()[1]) * 4096 >> 20
                r0 = rss(); b0 = sys.getallocatedblocks()
                n = gc.collect()
                print("     rss %d MB, small blocks %d; gc.collect freed %d objects -> rss %d MB" % (
                    r0, b0, n, rss()))
            if TM[0] and len(geng.STACK) > 1500:
                import tracemalloc
                snap = tracemalloc.take_snapshot()
                tot = sum(st.size for st in snap.statistics('filename'))
                print("     traced %d MB at depth %d; by line:" % (tot >> 20, len(geng.STACK)))
                for st in snap.statistics('lineno')[:12]:
                    print("       %6d KB %8d blocks  %s" % (st.size >> 10, st.count, st.traceback[0]))
                for st in snap.statistics('traceback')[:5]:
                    print("       %6d KB:" % (st.size >> 10), " <- ".join(str(f) for f in st.traceback))
            if len(geng.STACK) > 3000:   # what the deep descent is made of
                import resource
                st = geng.STACK; n = len(st)
                print("     maxrss %d MB; frames (name, q) at depth 0, n/4, n/2, 3n/4, n-1:" % (
                    resource.getrusage(resource.RUSAGE_SELF).ru_maxrss // 1024),
                    [(st[i][0], str(st[i][1])[:12]) for i in (0, n // 4, n // 2, 3 * n // 4, n - 1)])
                if os.environ.get('FRAMEMEM'):
                    framemem()
            sys.stdout.flush()


def framemem():
    """bytes held by the locals of the Python frames of the engine thread, by function (ints and one level of
    lists/tuples), to see what a deep descent keeps alive"""
    import collections
    seen = set()
    by = collections.Counter(); cnt = collections.Counter(); big = collections.Counter()
    for tid, f in sys._current_frames().items():
        if tid == threading.get_ident():
            continue
        while f is not None:
            nm = f.f_code.co_name
            cnt[nm] += 1
            for k, v in list(f.f_locals.items()):
                for o in ([v] + (list(v)[:64] if isinstance(v, (list, tuple)) else [])):
                    if id(o) in seen:
                        continue
                    seen.add(id(o))
                    z = sys.getsizeof(o)
                    by[nm] += z
                    if z > 2000:
                        big[(nm, k)] += z
            f = f.f_back
    print("     frames:", cnt.most_common(8))
    print("     bytes by function:", [(k, v >> 20) for k, v in by.most_common(8)], "MB")
    print("     big locals:", [(k, v >> 20) for k, v in big.most_common(10)], "MB")
    import gc
    ty = collections.Counter(); tz = collections.Counter()
    for o in gc.get_objects():
        t = type(o).__name__
        ty[t] += 1; tz[t] += sys.getsizeof(o)
    print("     gc objects:", [(k, ty[k], v >> 20) for k, v in tz.most_common(8)], "(type, count, MB)")
    ints = collections.Counter()
    for k in ('RULES', 'NEG', 'FULL', 'RRULES', 'RNEG', 'NRULES', 'NNEG', 'FROZEN', 'FPC', 'RUNRULES', 'EVTRACE'):
        ints[k] = len(getattr(geng, k))
    print("     tables:", dict(ints))


def sampler():
    """SAMPLE=1: a sampling profile of the engine thread (inclusive counts by function, and by caller->callee
    for discover), printed every 120 s"""
    import collections
    inc = collections.Counter(); n = 0; t0 = time.time()
    me = threading.get_ident()
    while True:
        time.sleep(0.02)
        for tid, f in sys._current_frames().items():
            if tid == me or f.f_code.co_name in ('status', 'sampler'):
                continue
            names = set(); chain = []
            while f is not None:
                names.add(f.f_code.co_name)
                if len(chain) < 3:
                    chain.append(f.f_code.co_name + ':%d' % f.f_lineno)
                f = f.f_back
            if 'main' not in names and 'main_prof' not in names:
                continue
            n += 1
            for nm in names:
                inc[nm] += 1
            inc['@' + ' < '.join(chain)] += 1
        if time.time() - t0 > 120 and n:
            print("     profile (%d samples):" % n, [(k, round(100 * v / n)) for k, v in inc.most_common(40)])
            sys.stdout.flush()
            inc.clear(); n = 0; t0 = time.time()


if os.environ.get('SAMPLE'):
    threading.Thread(target=sampler, daemon=True).start()
threading.Thread(target=status, daemon=True).start()
threading.stack_size(int(os.environ.get("STACKMB", "1024")) << 20)   # thread stack (counts toward ulimit -v)
def main_prof():
    import cProfile
    pr = cProfile.Profile()
    try:
        pr.runcall(main)
    finally:
        pr.dump_stats(os.environ['PROFILE'])


th = threading.Thread(target=main_prof if os.environ.get('PROFILE') else main)   # PROFILE=file: cProfile dump
th.start()
th.join()
