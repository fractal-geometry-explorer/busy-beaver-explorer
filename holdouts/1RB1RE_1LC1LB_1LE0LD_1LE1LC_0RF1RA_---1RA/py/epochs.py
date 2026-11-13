"""epochs.py MACHINE K STEPS STATE SIDE [MODE]: a run with bbtools.cycles (macro blocks of K cells, proved cycle
jumps), printing the tape as runs of 1s separated by single 0s (`a^k`: k runs of length a; a 0-run is an extra 0)
each time the head is at the SIDE (L/R) end of the tape in STATE and the block shape has changed since the last such
time.  MODE 'all': every such time; 'pre:TEXT': every such time the tape starts with TEXT.

The step counts are exact (the jumps apply Lean-checkable cycle rules, see tools/py/bbtools/cycles.py)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.cycles import Accelerator, snapshot
from bbtools.macro import MacroRun
from bbtools.machine import STATES

def runs_of(blocks):
    # blocks: list of (word str, count) left to right. Returns list of [len, mult] runs of ones; zeros between
    # consecutive runs: a run of length 0 means an extra 0.
    out = []  # list of [run, mult]
    cur = [0]  # current run length being built (ones), may merge
    def emit(r):
        if out and out[-1][0] == r: out[-1][1] += 1
        else: out.append([r, 1])
    def feed(w):
        for ch in w:
            if ch == '1': cur[0] += 1
            else: emit(cur[0]); cur[0] = 0
    for w, c in blocks:
        if c <= 6 or '0' not in w:
            if '0' not in w: cur[0] += len(w) * c
            else:
                for _ in range(c): feed(w)
        else:
            feed(w); feed(w)  # two copies, then periodic
            # after two copies, the state repeats: emit the runs of one copy (c-4) times
            before = len(out); snap = [list(x) for x in out]; cur0 = cur[0]
            feed(w)
            # runs emitted by one copy:
            # recompute: simplest is feed copies one at a time but bulk-add multiplicities
            # find runs added by the third copy relative to snap
            added = []
            # reconstruct difference
            tmp = [list(x) for x in out]
            # diff: compare tmp with snap
            i = 0
            while i < len(snap) - 1 and tmp[i] == snap[i]: i += 1
            # runs from position i in tmp beyond snap
            diff = []
            for j in range(i, len(tmp)):
                base = snap[j][1] if j < len(snap) and snap[j][0] == tmp[j][0] else 0
                diff.append((tmp[j][0], tmp[j][1] - base))
            if len(diff) == 1:
                out[-1][1] += diff[0][1] * (c - 4)
            else:
                # general: just feed (rare)
                for _ in range(c - 4): feed(w)
            feed(w)
    emit(cur[0])
    return out

def fmt(rs):
    # strip leading/trailing zero-runs
    while rs and rs[0][0] == 0: rs = rs[1:]
    while rs and rs[-1][0] == 0: rs = rs[:-1]
    s = []
    for r, m in rs:
        s.append(f"{r}" if m == 1 else f"{r}^{m}")
    return " ".join(s)

def tape_blocks(r):
    lw, rw = r.runs()
    return lw, rw

def main():
    M, K, N, S, SIDE = sys.argv[1], int(sys.argv[2]), int(float(sys.argv[3])), sys.argv[4], sys.argv[5]
    mode = sys.argv[6] if len(sys.argv) > 6 else 'shape'
    st = STATES.index(S)
    run = MacroRun(M, K)
    def at_end(r):
        if SIDE == 'R':
            return r.dir == 1 and len(r.right) == 1
        return r.dir == -1 and len(r.left) == 1
    acc = Accelerator(run)
    prev = None
    # custom loop replicating Accelerator.run with our printing
    from bbtools.cycles import HIST_KEYS
    while run.steps < N:
        if not run.step(): print("HALT", run.steps); break
        if acc.sample(run):
            s = snapshot(run)
            h = acc.hist.pop(s.key(), []); acc.hist[s.key()] = h
            if len(acc.hist) > HIST_KEYS: del acc.hist[next(iter(acc.hist))]
            h.append(s); del h[:-3]
            acc.jump(limit=N)
        if run.state == st and at_end(run):
            lw, rw = run.runs()
            key = tuple(w for w, c in lw + rw)
            if mode == 'all' or key != prev:
                print(run.steps, fmt(runs_of(lw + rw)), flush=True)
            elif mode.startswith('pre:'):
                t = fmt(runs_of(lw[:3] + rw[:3]))
                if t.startswith(mode[4:]): print(run.steps, fmt(runs_of(lw + rw)), flush=True)
            prev = key
    print("END", run.steps)
main()
