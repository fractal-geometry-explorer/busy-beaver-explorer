"""Check the accelerated simulator against direct simulation:
    gcc -O2 -o wv ../c/wv.c
    ./wv <machine> 3e6 0 1 > ref.txt                      (every wall visit of the first 3*10^6 steps)
    python3 accel_check.py <1|2> ref.txt [more files] [mjN]

Every wall visit listed in the files is compared: the word right of the wall and the step count.  Without mjN the
outer wall advances one listed visit at a time (visits of sub-tapes are still jumped); with mjN every jump is at most
N visits and only the visits where the simulator lands are compared.  Files for later stretches come from
../c/wv2.c (wv2 <machine> <from step> <count>)."""
import sys, time, threading
sys.set_int_max_str_digits(0)
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import msim, geng
from msim import Macro
from geng import to_digits
M1 = "1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA"
M2 = "1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA"


def main():
    M = M1 if sys.argv[1] == '1' else M2
    MJ = int(sys.argv.pop()[2:]) if sys.argv[-1].startswith('mj') else None
    ref = {}
    for f in sys.argv[2:]:
        for line in open(f):
            p = line.split()
            if p[0] in ('RIGHT', 'HALT'):
                continue
            c = p[3]
            if len(c) % 2:
                c += '0'
            w = ''.join({'10': 'X', '11': 'Y', '00': 'O', '01': 'Z'}[c[i:i + 2]] for i in range(0, len(c), 2))
            ref[int(p[0])] = ([len(x) for x in w.split('X')] if set(w) <= set('XY') else w, int(p[1]))
    mm = Macro(M)
    mm.maxjump = MJ
    mm.top_targets = sorted(ref) if MJ is None else [max(ref)]
    res = [0, 0]

    def on_top(m, toks):
        v = m.topv
        if v in ref:
            d = to_digits(toks) if toks is not None else None
            st = m.steps - 1 if not m.landed else m.steps
            if d == ref[v][0] and st == ref[v][1]:
                res[0] += 1
            else:
                res[1] += 1
                if res[1] < 5:
                    print("MISMATCH at visit", v, str(d)[:300], str(ref[v])[:300], m.steps)
    mm.on_top = on_top
    t = time.time()
    last = max(ref)
    mm.run(until=lambda m: m.topv >= last)
    print("visits compared: %d equal (word and step count), %d different, of %d listed; %d hooks, %d macro steps, "
          "%.1fs; engine %s" % (res[0], res[1], len(ref), mm.hooks, mm.msteps, time.time() - t, geng.STATS))


threading.stack_size(1 << 30)
th = threading.Thread(target=main)
th.start()
th.join()
