"""The run of 1RB1RF_1LC1LB_1RD1LD_1RE0RA_---0LB_0LF0RC on run lists (rls.py with this machine's oracle).

usage: python3 runlist.py check [STEPS]        every visit of the left end in state D of the plain machine (c/dv.c,
                                               default 3e9 steps) against the run-list simulator: tape and step count
       python3 runlist.py accel DFORMS [N]     the same against the visits written by dforms.py (accelerated macro run)
       python3 runlist.py events EXP           the events (visits after which the block of 2s is rebuilt) to 10^EXP steps
       python3 runlist.py exhaust J0 J1 [K2]   what happens when the first counter runs out: the configuration of
                                               step ~10^27 with its first counter set to J (J0 <= J < J1), 80 events each
       python3 runlist.py rule CONFIG          the learned rule for the shape of a configuration, large counts as letters
       python3 runlist.py halt CONFIG          run a configuration given as a run list, e.g. "0 3 2^8 3^20 1 3^6 1"

The C programs are compiled into a temporary directory on first use.
"""
import os
import re
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rls import RLS, Runner, canon, fmt, parse  # noqa: E402

M = "1RB1RF_1LC1LB_1RD1LD_1RE0RA_---0LB_0LF0RC"
START, START_STEPS = "0 3 2^2 3^3 0 3 0 3 1", 390       # the visit at step 390 (dv prints it)
# the visit after event 69 (about 1.1e27 steps), with the first counter and the last one as parameters
LATE = "0 3 2^6142393098362 3^6142393098366 (1 3)^59 3^5520119233849 0 3^{J} 4 3^{K2} 1"


def build(name):
    d = os.path.join(tempfile.gettempdir(), "rls-279")
    os.makedirs(d, exist_ok=True)
    exe = os.path.join(d, name)
    src = os.path.join(HERE, "..", "c", name + ".c")
    if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(src):
        subprocess.run(["gcc", "-O2", "-o", exe, src], check=True)
    return exe


def new_rls(m=2):
    return RLS(M, "D", m=m, exe=build("syn"))


def short(n):
    s = str(n)
    return s if len(s) <= 14 else f"{s[:4]}..({len(s)}d)"


def sfmt(tokens):
    def one(p, c):
        s = short(p[0]) if len(p) == 1 else "(" + " ".join(map(short, p)) + ")"
        return s if c == 1 else f"{s}^{short(c)}"
    return " ".join(one(p, c) for p, c in tokens)


def twos(tokens):
    return tokens[2][1] if len(tokens) > 2 and tokens[2][0] == (2,) else 0


def check(steps=3e9):
    out = subprocess.run([build("dv"), M, str(steps), "D"], capture_output=True, text=True).stdout.split("\n")
    ref = {}
    for line in out:
        f = line.split(None, 1)
        if len(f) == 2:
            ref[int(f[0])] = f[1]
    R = new_rls()
    run = Runner(R, parse(START), steps=START_STEPS)
    ok = bad = 0
    last = max(ref)
    run.limit = last
    while run.steps < last and run.step():
        if run.steps in ref:
            if fmt(canon(parse(ref[run.steps]))) == fmt(run.tokens):
                ok += 1
            else:
                bad += 1
    print(f"{len(ref)} visits of the plain machine in {last} steps; the run-list simulator made {run.visits} visits "
          f"({run.jumps} jumps, {len(R.rules)} learned rules) and stood on {ok + bad} of them: {ok} equal, {bad} different")
    return bad == 0 and ok > 0


def accel(path, maxn=None):
    refs = []
    for line in open(path):
        f = line.split(None, 3)
        if f[0] == "END":
            continue
        st = int(f[0]) - {"D": 0, "B": 3, "C": 4}[f[1]]
        refs.append((st, re.sub(r"( 0\^\d+| 0)+$", "", f[3].strip())))
    refs = refs[:maxn]
    R = new_rls()
    run = Runner(R, parse(START), steps=START_STEPS)
    ok = bad = miss = 0
    for st, s in refs:
        if st < run.steps:
            continue
        run.limit = st
        while run.steps < st and run.step():
            pass
        if run.steps != st:
            miss += 1
        elif fmt(run.tokens) == fmt(canon(parse("0 " + s))):
            ok += 1
        else:
            bad += 1
    print(f"{len(refs)} visits of the accelerated macro run, the last at {float(refs[-1][0]):.3e} steps: {ok} equal "
          f"(tape and step count), {bad} different, {miss} not met; {len(R.rules)} learned rules, {run.jumps} jumps")
    return bad == 0 and miss == 0


def events(limexp, start=START, steps=START_STEPS, maxev=None, quiet=False, R=None):
    R = R or new_rls()
    r = Runner(R, parse(start), steps=steps)
    t0, prevn, nev, log = time.time(), 0, 0, []
    lim = None if limexp is None else 10 ** limexp
    while (lim is None or r.steps < lim) and (maxev is None or nev < maxev):
        before, bs = r.tokens, r.steps
        if not r.step():
            break
        n = twos(r.tokens)
        if n < prevn - 1:
            nev += 1
            log.append((before, r.tokens))
            if not quiet:
                print(f"{nev} 1e{len(str(bs)) - 1} | {sfmt(before)}\n   -> {sfmt(r.tokens)}", flush=True)
        prevn = n
    if not quiet:
        print(f"{'HALTED after ' + str(r.steps) if r.halted else 'running at ' + short(r.steps)} steps; {nev} events, "
              f"{len(R.rules)} learned rules, {r.jumps} jumps, {time.time() - t0:.0f} s\n   {sfmt(r.tokens)}")
    return r, nev, log


def exhaust(j0, j1, k2="103352228710"):
    R = new_rls()
    for j in range(j0, j1):
        r, nev, log = events(None, LATE.format(J=j, K2=k2), 0, maxev=80, quiet=True, R=R)
        print(f"J={j}: " + (f"HALTS after {nev} events, {short(r.steps)} more steps" if r.halted else
                            f"runs on ({nev} events): {sfmt(r.tokens)}"), flush=True)


def describe(cfg, names="npabcdefgh"):
    """the learned rule of the shape of `cfg`, with the large counts as letters (in the order they occur)"""
    R = new_rls()
    toks = canon(parse(cfg))
    key, vals = R.shape(toks)
    R.apply(toks)
    r = R.rules[key]
    if r == "FAIL" or any(v < b for v, b in zip(vals, r.base)):
        return "no single rule (counts too small for the shape)"
    it = iter(names)
    def nm(slot, lit):
        return f"{next(it)}" if isinstance(slot, tuple) else str(lit)
    lhs = []
    for (kp, kc), (p, c) in zip(key, toks):
        ps = [nm(a, b) for a, b in zip(kp, p)]
        cs = nm(kc, c)
        s = ps[0] if len(ps) == 1 else "(" + " ".join(ps) + ")"
        lhs.append(s if cs == "1" else f"{s}^{cs}")
    par = ", ".join(f"{names[i]} = {v % R.m} mod {R.m}" for i, v in enumerate(vals))
    if r.kind == "HALT":
        return " ".join(lhs) + "  ->  HALT   [" + par + "]"
    def expr(f):
        f0, a = f
        c0 = f0 - sum(ai * b for ai, b in zip(a, r.base))
        parts = []
        for ai, nme in zip(a, names):
            if ai == 0:
                continue
            parts.append((("" if ai == 1 else ("-" if ai == -1 else str(ai))) + nme))
        if c0 != 0 or not parts:
            parts.append(str(c0))
        return "+".join(parts).replace("+-", "-")
    rhs, i = [], 0
    for L in r.struct:
        ps = [expr(f) for f in r.out[i:i + L]]
        cs = expr(r.out[i + L])
        i += L + 1
        s = ps[0] if len(ps) == 1 else "(" + " ".join(ps) + ")"
        if cs == "0":
            continue
        rhs.append(s if cs == "1" else f"{s}^({cs})" if not cs.isdigit() else f"{s}^{cs}")
    return " ".join(lhs) + "  ->  " + " ".join(rhs) + "   [" + par + "]"


def halt(cfg):
    r = Runner(new_rls(), parse(cfg))
    while r.visits < 10 ** 6 and r.step():
        pass
    print(f"halts after {r.steps} steps" if r.halted else f"no halt in {r.visits} visits: {sfmt(r.tokens)}")


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[:1] == ["check"]:
        sys.exit(0 if check(*[float(x) for x in a[1:2]]) else 1)
    elif a[:1] == ["accel"] and len(a) > 1:
        sys.exit(0 if accel(a[1], *[int(x) for x in a[2:3]]) else 1)
    elif a[:1] == ["events"] and len(a) > 1:
        events(int(a[1]))
    elif a[:1] == ["exhaust"] and len(a) > 2:
        exhaust(int(a[1]), int(a[2]), *a[3:4])
    elif a[:1] == ["rule"] and len(a) > 1:
        print(describe(a[1]))
    elif a[:1] == ["halt"] and len(a) > 1:
        halt(a[1])
    else:
        sys.exit(__doc__)
