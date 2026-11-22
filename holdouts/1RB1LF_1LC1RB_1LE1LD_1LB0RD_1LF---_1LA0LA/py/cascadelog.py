"""Log the cascades of the accelerated run inside a right-end event's return:  python3 cascadelog.py EVENT SECONDS

Runs the accelerated simulator (msim + geng, as accel_run.py 1) to the given right-end event; from the visit of the
event on, every block transition is simulated cell by cell (no memo), and every cascade (a pass of the head where F
flips a 1 and A then reads a 0, see cascade.py) is printed with m, the number of blank cells left of the turning
pair (inf: only blank tape), and every hand-over of wall visits to the digit engine with the number of visits
offered (M = 1 + blank pairs to the left) and made (m < M: the visits end in an event).
"""
import sys, os, time, threading
sys.set_int_max_str_digits(0)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import msim, geng
from msim import Macro

MACH = "1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA"
ON = [False]
LOG = []
PREV = [None]
PROBE = [None]      # while a crossing of repeated blocks is being tried: the cascades of the one-copy run


def report(m, step, times=1):
    LOG.append(("CASCADE", m, step, times))
    print("  cascade m = %s%s   (step %s)" % (m, "" if times == 1 else "  x %d (a run of %d equal blocks)" % (times, times),
                                             step), flush=True)


def main():
    target = int(sys.argv[1])
    secs = float(sys.argv[2])
    cap = 100
    mm = Macro(MACH)
    mm.topcap = 10 ** cap
    ev = [0]
    t0 = time.time()
    orig_runwin = Macro.runwin
    orig_trans = Macro.trans

    def runwin(self, s, cells, pos, skip_first, hook):
        if not ON[0]:
            return orig_runwin(self, s, cells, pos, skip_first, hook)
        T = self.T
        n = len(cells)
        steps = 0
        while 0 <= pos < n:
            r = cells[pos]
            if hook and s == 0 and r == 0 and not skip_first:
                if (pos + 1 >= n or cells[pos + 1] == 1) and (pos < 1 or cells[pos - 1] == 0) and \
                        (pos < 2 or cells[pos - 2] == 0):
                    PREV[0] = None
                    return 'C', s, pos, steps
            skip_first = False
            if PREV[0] == (5, 1) and s == 0 and r == 0:
                if PROBE[0] is not None:
                    q = pos - 1
                    while q >= 0 and cells[q] == 0:
                        q -= 1
                    PROBE[0].append(pos - 1 - q if q >= 0 else ">=%d" % pos)
                else:
                    z = self.left_zeros("".join(map(str, cells[:pos])))
                    report("inf" if z is None else z, self.steps + steps)
            tr = T[s][r]
            if tr is None:
                PREV[0] = (s, r)
                return 'H', s, pos, steps
            PREV[0] = (s, r)
            cells[pos] = tr[0]
            pos += tr[1]
            s = tr[2]
            steps += 1
        return ('L' if pos < 0 else 'R'), s, pos, steps

    def trans(self, s, d, faced, behind):
        if not ON[0]:
            return orig_trans(self, s, d, faced, behind)
        K = self.K
        if d == 1:
            cells = self.bits(behind) + self.bits(faced); pos = K
        else:
            cells = self.bits(faced) + self.bits(behind); pos = K - 1
        kind, s2, pos2, st = self.runwin(s, cells, pos, False, self.hook)
        return (kind, s2, self.val(cells[:K]), self.val(cells[K:]), pos2, st)

    def finish(self, kind, s2, lb, rb, pos, st, s, d, faced):
        # msim.Macro.finish, with the cascades inside a crossing of n equal blocks reported n times
        L, R = self.L, self.R
        self.steps += st
        if not R and (self.pend or self.lazy is not None):
            self.fill()
        if kind in ('R', 'L'):
            if kind == 'R':
                self.push(L, lb); self.push(L, rb); self.s = s2; self.dir = 1
                rep = d == 1 and s2 == s and R and R[-1][0] == faced
            else:
                self.push(R, rb); self.push(R, lb); self.s = s2; self.dir = 0
                rep = d == 0 and s2 == s and L and L[-1][0] == faced
            if rep:
                n = (R if kind == 'R' else L)[-1][1]
                PROBE[0] = []; save = PREV[0]
                r = self.trans(s, 1 if kind == 'R' else 0, faced, rb if kind == 'R' else lb)
                got = PROBE[0]; PROBE[0] = None; PREV[0] = save
                ok = (r[0] == 'R' and r[1] == s and r[3] == rb) if kind == 'R' else (r[0] == 'L' and r[1] == s and r[2] == lb)
                if ok:
                    if kind == 'R':
                        R.pop(); self.pop(L); self.push(L, r[2], n); self.push(L, rb)
                    else:
                        L.pop(); self.pop(R); self.push(R, r[3], n); self.push(R, lb)
                    if got and ON[0]:
                        for g in got:
                            report(g, self.steps, n)
                    self.steps += n * r[5]
        elif kind == 'H':
            self.push(L, lb); self.push(R, rb)
            self.s = s2
            self.steps += 1
            self.halt_pos = pos
            raise msim.Halt()
        else:
            self.candidate(s2, lb, rb, pos)

    Macro.runwin = runwin
    Macro.trans = trans
    Macro.finish = finish

    def trace(m, mv, toks, T2):
        if ON[0]:
            M = m.last_call[0] if hasattr(m, 'last_call') else None
            Ms = "inf" if M is not None and M >= msim.INF else (str(M) if M is not None and len(str(M)) < 30 else "big")
            mvs = str(mv) if len(str(mv)) < 30 else "%d digits" % len(str(mv))
            LOG.append(("HOOK", Ms, mvs))
            print("  hook: %s wall visits offered, %s made%s%s" % (Ms, mvs, "  (ends in an event)" if (M is not None and mv < M) else "",
                                                               "  [outer wall]" if m.landed else ""), flush=True)
        if m.landed:
            if mv < m.topcap:
                ev[0] += 1
                print("[%.0fs] EVENT %d at the next outer wall visit (visit %d digits, step %d digits)" % (
                    time.time() - t0, ev[0], len(str(m.topv)), len(str(m.steps))), flush=True)
                m.topcap = 10 ** cap
                if ev[0] == target:
                    ON[0] = True
                    m.memo.clear()
                    PREV[0] = None
                    print("logging cascades from here", flush=True)
            elif m.topcap < 10 ** 20000:
                m.topcap = min(m.topcap * m.topcap, 10 ** 20000)
    mm.trace = trace
    while time.time() - t0 < secs:
        try:
            r = mm.run(max_msteps=mm.msteps + 200)
        except (RecursionError, MemoryError):
            print("engine out of depth/memory"); break
        if r == 'halt':
            print("HALT: state %s, wall visits %d digits" % ("ABCDEF"[mm.s], len(str(mm.topv))), flush=True)
            break
    n = sum(1 for x in LOG if x[0] == "CASCADE")
    print("end: %.0fs, %d cascades logged, %d hooks after the event" % (time.time() - t0, n, sum(1 for x in LOG if x[0] == "HOOK")))


threading.stack_size(int(os.environ.get("STACKMB", "1024")) << 20)
th = threading.Thread(target=main)
th.start()
th.join()
