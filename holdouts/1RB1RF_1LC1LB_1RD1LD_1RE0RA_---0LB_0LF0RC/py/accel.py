"""Exact accelerated runs of 1RB1RF_1LC1LB_1RD1LD_1RE0RA_---0LB_0LF0RC: `ctxmacro.CtxMacroRun` (blocks of 12 cells)
driven by `bbtools.cycles.Accelerator`, which proves each linear cycle rule with `bbtools.symtm` before jumping.

usage: python3 accel.py run MAXEXP [LOG]     run to 10^MAXEXP steps; a line per decade (and the jumps, to LOG)
       python3 accel.py epochs LIMIT         the tape (as words) just before and after each epoch change, to LIMIT steps
       python3 accel.py check [STEPS]        the accelerated run against the plain macro run (default 10^12 steps)

Words: b = 011, c = 1011, d = 1110, e = 10, u = 1011 1010 1110 (= c e e d).
"""
import os
import re
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "../../../tools/py"))
from bbtools.cycles import HIST_KEYS, Accelerator, at_tape_end, snapshot  # noqa: E402
from ctxmacro import M, CtxMacroRun  # noqa: E402

K = 12
WORDS = [("u", "101110101110"), ("c", "1011"), ("b", "011"), ("d", "1110"), ("e", "10")]
CAP = 8


def tokens(r):
    """The tape, left to right, as words; a long run is tokenized from CAP copies and its count restored."""
    runs = [(x, c) for x, c in r.left[1:]] + [(x, c) for x, c in reversed(r.right[1:])]
    s, reg, n = [], [], 0
    for x, c in runs:
        w = "".join(map(str, x))
        cc = min(c, CAP)
        if c > cc:
            reg.append((n, n + cc * len(w), c - cc, len(w)))
        s.append(w * cc)
        n += cc * len(w)
    s = "".join(s)
    i = len(s) - len(s.lstrip("0"))
    s2 = s.rstrip("0")
    out = []
    while i < len(s2):
        for nm, w in WORDS:
            if s2.startswith(w, i):
                st, k = i, 0
                while s2.startswith(w, i):
                    i += len(w)
                    k += 1
                out.append([nm, k, st, i, len(w)])
                break
        else:
            if out and out[-1][0] == s2[i] and out[-1][3] == i:
                out[-1][1] += 1
                out[-1][3] += 1
            else:
                out.append([s2[i], 1, i, i + 1, 1])
            i += 1
    bad = []
    for a, b, extra, wl in reg:
        mid = (a + b) // 2
        for t in out:
            if t[2] <= mid < t[3] and t[1] >= 3 and (extra * wl) % t[4] == 0 and t[3] - t[2] >= 2 * wl:
                t[1] += extra * wl // t[4]
                break
        else:
            bad.append(f" [+{extra} more of {s[a:a + wl]}]")
    return " ".join(nm if k == 1 else f"{nm}^{k}" for nm, k, _, _, _ in out) + "".join(bad)


def sampled(a, limit):
    """Drive the accelerator as `Accelerator.run` does, yielding the run at every sample point."""
    r = a.run_
    while r.steps < limit and r.step():
        if at_tape_end(r):
            yield r
            s = snapshot(r)
            h = a.hist.pop(s.key(), [])
            a.hist[s.key()] = h
            if len(a.hist) > HIST_KEYS:
                del a.hist[next(iter(a.hist))]
            h.append(s)
            del h[:-3]
            a.jump(limit=limit)


def run(maxexp, log=None):
    a = Accelerator(CtxMacroRun(M, K))
    r, t0, nj = a.run_, time.time(), 0
    f = open(log, "w") if log else None
    for e in range(3, maxexp + 1):
        a.run(10 ** e)
        if f:
            for before, n, after, name in a.jumps[nj:]:
                f.write(f"J {before} {n} {after} {name}\n")
            nj = len(a.jumps)
            f.write(f"C {r.steps} {tokens(r)}\n")
            f.flush()
        print(f"10^{e}: {'HALTED' if r.halted else 'no halt'} at {r.steps} steps; {r.msteps} macro steps, "
              f"{len(a.rules)} proved rules, {len(a.jumps)} jumps, {len(a.failed)} failed proofs, "
              f"{time.time() - t0:.0f} s", flush=True)
        if r.halted:
            print(r.halt_info)
            break


def epochs(limit):
    a = Accelerator(CtxMacroRun(M, K))
    prev, prevn = None, -1
    for r in sampled(a, limit):
        if r.dir != -1:
            continue
        t = tokens(r)
        m = re.search(r"b\^(\d+)", t[:40])
        n = int(m.group(1)) if m else 0
        if n < prevn // 2:
            print("end  ", prev[0], prev[1])
            print("start", r.steps, t, flush=True)
        prev, prevn = (r.steps, t), n
    print("halted" if a.run_.halted else "running", a.run_.steps)


def check(steps=10 ** 12):
    a = Accelerator(CtxMacroRun(M, K)).run(steps)
    p = CtxMacroRun(M, K)
    while p.steps < a.run_.steps and p.step():
        pass
    same = (p.steps == a.run_.steps and p.state == a.run_.state and p.head() == a.run_.head()
            and p.left[1:] == a.run_.left[1:] and p.right[1:] == a.run_.right[1:])
    print(f"{a.run_.steps} steps, {len(a.jumps)} jumps of {len(a.rules)} rules: "
          f"{'same configuration as the plain macro run' if same else 'MISMATCH'}")
    return same


if __name__ == "__main__":
    if len(sys.argv) > 2 and sys.argv[1] == "run":
        run(int(sys.argv[2]), sys.argv[3] if len(sys.argv) > 3 else None)
    elif len(sys.argv) > 2 and sys.argv[1] == "epochs":
        epochs(int(float(sys.argv[2])))
    elif len(sys.argv) > 1 and sys.argv[1] == "check":
        check(*[int(float(x)) for x in sys.argv[2:3]])
    else:
        sys.exit(__doc__)
