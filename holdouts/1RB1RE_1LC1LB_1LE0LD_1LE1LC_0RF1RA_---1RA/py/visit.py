"""The visit map of 1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA on run lists, and its checks against the machine.

The tape is a list of runs of 1s separated by single 0s.  A *visit* is the moment B stands on the blank cell just
left of the tape.  `visit(l)` gives the list at the next visit, or None: the machine halts (every run even).
`cascC`, `cascB`, `scan`, `visit_lean` mirror the definitions of lean/Visit.lean one to one; `visit` is the same map
written as a loop.  `inD` is the domain D of lean/Visit.lean (entered at step 423, never left).

usage: python3 visit.py check STEPS     both forms of the map against the machine (py/runstack.py) at every visit
       python3 visit.py orbit N         the first N lists of the orbit of l0 = [12, 1^9] under the map alone
       python3 visit.py epochs N        N epochs with the run-stack simulator (sweeps in bulk); statistics of how
                                        deep into the stack each epoch reaches
"""
import sys, os, collections, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

L0 = [12] + [1] * 9


def inD(l):
    return (len(l) >= 1 and all(r >= 1 and r != 2 for r in l) and l[0] % 2 == 0
            and (l[0] >= 12 or (len(l) >= 4 and l[:4] == [6, 4, 1, 1])))


def visit(l):
    """the next list, or None (the machine halts)"""
    r = list(l); r[0] += 2
    j = next((i for i, x in enumerate(r) if x % 2), None)
    if j is None: return None                        # all runs even: E reaches the right end, F reads 0
    if j == len(r) - 1:                              # the first odd run is the last run
        t = (r[j] + 1) // 2; W = 1; rest = []; i = j
    else:                                            # it is joined with the run after it
        W = r[j] + r[j + 1] + 2; rest = r[j + 2:]; i = j - 1; t = r[i] // 2
    while True:                                      # the cascade to the left, two even runs at a time
        if i == 0:
            assert t >= 5
            return [6, 4] + [1] * (t - 5) + [W] + rest
        if t >= 2: a = r[i - 1] + 4; rest = [1] * (t - 2) + [W] + rest
        else: a = r[i - 1] + 3 + W
        if i - 1 == 0: return [a] + rest
        W = 1 + a; t = r[i - 2] // 2; i -= 2


def cascC(hs, l):
    if not hs: return [6, 4] + l[5:]
    g = l[1] if len(l) > 1 else 1
    if len(hs) == 1: return [2 * hs[0] + 3 + g] + l[2:]
    return cascC(hs[2:], [1] * hs[1] + [2 * hs[0] + 4 + g] + l[2:])


def cascB(hs, l):
    if not hs or not l: return l
    return cascC(hs[1:], [1] * hs[0] + [l[0] + 1] + l[1:])


def scan(hs, l):
    while True:
        if not l: return None
        r = l[0]
        if r % 2 == 0: hs = [r // 2] + hs; l = l[1:]; continue
        if len(l) == 1: return cascC(hs, [1] * ((r + 1) // 2) + [1])
        return cascB(hs, [r + l[1] + 1] + l[2:])


def visit_lean(l):
    return scan([(l[0] + 2) // 2], l[1:])


def flat(R):
    l = []
    for a, m in reversed(R): l += [a] * m
    return l


def check(N):
    from runstack import Sim
    s = Sim(); cur = None; n = 0; first = None
    while s.steps < N:
        if s.at_visit():
            l = flat(s.R)
            if cur is not None:
                assert cur == l, ("the map is wrong at step", s.steps); n += 1
            if inD(l):
                if first is None: first = s.steps
                cur = visit(l)
                assert cur == visit_lean(l), ("the two forms differ", l[:20])
            else:
                assert first is None, ("left D at step", s.steps)
        if not s.step(): print("HALT at step", s.steps + 1); break
    print("visits predicted correctly: %d (both forms of the map); first visit in D at step %d, D never left" % (n, first))


def orbit(N):
    l = L0
    for i in range(N):
        print(i, ' '.join(map(str, l[:40])), '...' if len(l) > 40 else '')
        l = visit(l)
        if l is None: print("HALT"); return
        assert inD(l)


def epochs(NE):
    from runstack import Sim
    s = Sim(); ne = 0; minR = None; start = None; hist = collections.Counter(); t0 = time.time(); low = []
    while ne < NE:
        if s.at_visit():
            R = s.R
            if len(R) >= 3 and R[-1] == [6, 1] and R[-2] == [4, 1] and R[-3][0] == 1:     # [6, 4, u^m, L]
                if start is not None and ne > 100: hist[start - minR] += 1
                ne += 1; start = len(R) - 3; minR = start; low.append(start)
            s.sweep()
        if not s.step(): print("HALT at step", s.steps + 1); return
        if minR is not None and len(s.R) < minR and s.d == 1: minR = len(s.R)
    print("epochs", ne, "| steps: a number of", s.steps.bit_length(), "bits | stack entries (run, count):", len(s.R),
          "| runs:", sum(m for l, m in s.R), "| no halt | %.0f s" % (time.time() - t0))
    tot = sum(hist.values())
    print("entries of the stack L passed by the head in one epoch: epochs (share)")
    for k in sorted(hist): print("  %d: %d (%.1e)" % (k, hist[k], hist[k] / tot))
    fut = [0] * len(low); m = 10 ** 9
    for i in range(len(low) - 1, -1, -1):
        m = min(m, low[i]); fut[i] = low[i] - m
    c = collections.Counter(fut[:len(fut) // 2])
    print("how far the stack later drops below its size at an epoch start (entries): epochs (first half of the run)")
    for k in sorted(c): print("  %d: %d" % (k, c[k]))


if __name__ == "__main__":
    mode, n = sys.argv[1], int(float(sys.argv[2]))
    {"check": check, "orbit": orbit, "epochs": epochs}[mode](n)
