"""Epoch map of 1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC by symbolic runs, and the inner counter of the S1 epochs.

An *epoch* is the tape  E(n, S) = <A> (01111)^n S  (blank elsewhere, S a short tail).  A *class* is (S, r, m): all
E(n, S) with n = r mod m and n >= THR.  For a class the engine of accel.py runs with n = r0 + m x, x >= 0 free, until
the next epoch.  The engine refuses every step whose outcome depends on x, so a run that ends at E(k + c x, S') holds
for every x.  When a cycle rule would be applied a number of times that is not affine in x the class is split.

usage (from the repo root; D = holdouts/1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC/py/closure):
  python3 D/epochmap.py classes [OUT.json]   the classes of the eight tails S0..S7 (S1 does not resolve: see README)
  python3 D/epochmap.py validate CLASSES.json  every class at x = 0 and x = 1 against the plain C simulator
                                             c/epochs.c (next n, next tail and step count must be equal)
  python3 D/epochmap.py run SECONDS          epochs of the run from blank tape (accelerated, exact)
  python3 D/epochmap.py s1 N [TAIL]          one epoch from E(N, S1), printing the tape right of the big block each
                                             time the count of (110011) changes: the binary counter
  python3 D/epochmap.py s1map N0 N1          next epoch from E(n, S1) for n in [N0, N1) (numbers, exact)
  python3 D/epochmap.py unwind SEED SAMPLES MAXDIGITS
                                             random counter words: is the unwinding a finite-state process?
"""
import collections
import json
import os
import random
import re
import subprocess
import sys
import time
from fractions import Fraction
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import accel  # noqa: E402
from accel import Driver, Lin, NeedSplit, Pol, Sim, Undecided, compress, fmt, parse  # noqa: E402

WORD = (0, 1, 1, 1, 1)
THR = 2000
ENVX = 10 ** 9 + 7   # value of x used only to *look for* cycles (the rules found are proved for all values)
TAILS = {"S0": "0011110111110111", "S1": "00111101111001", "S2": "0011110111101111001111000111",
         "S3": "001111011110111", "S4": "0011110111100111", "S5": "00111101111001100111",
         "S6": "0011110111110011110111", "S7": "0011110111101111001"}
NAME = {v: k for k, v in TAILS.items()}


def cells(toks):
    out = []
    for t in toks:
        if t == 'H':
            continue
        if isinstance(t, list):
            out.extend(t[0] * t[1])
        else:
            out.append(t)
    return out


def is_epoch(toks, symbolic):
    """(tail, n) if the tape after the head is (01111)^n tail with exactly one big repeat, else None.
    symbolic: the big repeat is the one whose count carries the variable; otherwise the first repeat >= 20."""
    toks = [t for t in toks if t != 'H']
    lin = [i for i, t in enumerate(toks) if isinstance(t, list) and isinstance(t[1], Lin)]
    if symbolic:
        if len(lin) != 1:
            return None
        i = lin[0]
    else:
        if lin:
            return None
        big = [i for i, t in enumerate(toks) if isinstance(t, list) and t[1] >= 20]
        if not big:
            return None
        i = big[0]
    if i != 0 or tuple(toks[0][0]) != WORD:
        return None
    n = toks[0][1]
    post = cells(toks[1:])
    while tuple(post[:5]) == WORD:
        del post[:5]
        n = n + 1
    while post and post[-1] == 0:
        post.pop()
    if len(post) > 60:
        return None
    return ''.join(map(str, post)), n


def start(tail, count):
    s = Sim()
    s.st = accel.EVSTATE
    s.L = []
    s.R = list(reversed([[WORD, count]] + [int(c) for c in tail]))
    s.steps = Lin(0) if isinstance(count, Lin) else 0
    s.recompress()
    return s


def run_class(tail, r, m, rules, max_moves=20000000):
    r0 = THR + (r - THR) % m
    d = Driver(start(tail, Lin(r0, {0: m})), True)
    d.rules = rules
    d.env = {0: ENVX}
    out = {}

    def on_event(d, toks):
        nd = is_epoch(toks, True)
        if nd is None:
            return False
        out["tail"], out["count"] = nd
        return True

    try:
        d.run(None, on_event, max_moves=max_moves)
    except NeedSplit as e:
        return dict(kind="split", d=e.d, r0=r0, why=str(e))
    except Undecided as e:
        return dict(kind="undecided", r0=r0, why=str(e))
    if d.s.halt:
        return dict(kind="halt", r0=r0, steps=repr(d.s.steps))
    if not out:
        return dict(kind="undecided", r0=r0, why="no epoch within %d moves" % d.moves)
    n = out["count"]
    st = Pol.of(d.s.steps)
    return dict(kind="epoch", r0=r0, to=out["tail"], k=n.k, c=n.c[0], steps=[str(a) for a in st.a], moves=d.moves)


def classes(out=None):
    rules = {}
    res = []

    def explore(name, tail, r, m, depth=0):
        x = run_class(tail, r, m, rules)
        if x["kind"] == "split" and depth < 4:
            m2 = m * x["d"] // gcd(m, x["d"])
            for j in range(m2 // m):
                explore(name, tail, (r + m * j) % m2, m2, depth + 1)
            return
        x.update(tail=name, r=r, m=m)
        res.append(x)
        if x["kind"] == "epoch":
            off = x["k"] - Fraction(x["c"], m) * x["r0"]
            print("%s  n = %d + %d x  ->  %s  n' = %d + %d x   (n' = %s n %s %s)" % (
                name, x["r0"], m, NAME.get(x["to"], x["to"]), x["k"], x["c"], Fraction(x["c"], m),
                "-" if off < 0 else "+", abs(off)), flush=True)
        else:
            print("%s  n = %d mod %d: %s (%s)" % (name, r, m, x["kind"], x.get("why", x.get("steps"))), flush=True)

    for name, tail in TAILS.items():
        explore(name, tail, 0, 1)
    if out:
        json.dump(dict(machine=accel.MACHINE, thr=THR, tails=TAILS, classes=res), open(out, "w"), indent=1)
    return res


def c_exe():
    exe = "/tmp/epochs_M2"
    if not os.path.exists(exe):
        subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(HERE, "..", "..", "c", "epochs.c")], check=True)
    return exe


def plain_next(n, tail, steps=10 ** 12):
    p = subprocess.Popen([c_exe(), accel.MACHINE, str(steps), "01111" * n + tail], stdout=subprocess.PIPE, text=True)
    try:
        for line in p.stdout:
            f = line.split()
            if f[0] in ("HALT", "END", "OUT"):
                return (f[0],)
            if int(f[1]) > n + 10:
                return int(f[0]), int(f[1]), f[2] if len(f) > 2 else ""
    finally:
        p.kill()
    return ("END",)


def validate(path):
    cert = json.load(open(path))
    bad = n = 0
    for c in cert["classes"]:
        if c["kind"] != "epoch":
            continue
        pol = Pol([Fraction(a) for a in c["steps"]])
        for x in (0, 1):
            got = plain_next(c["r0"] + c["m"] * x, cert["tails"][c["tail"]])
            want = (pol.at(x), c["k"] + c["c"] * x, c["to"])
            n += 1
            if got != want:
                bad += 1
                print("MISMATCH", c["tail"], c["r0"], x, got, want)
    print("%d runs of the plain simulator compared with the classes, %d mismatches" % (n, bad))
    return bad == 0


def real_run(seconds):
    d = Driver()
    t0 = time.time()

    def on_event(d, toks):
        nd = is_epoch(toks, False)
        if nd is not None:
            print("step %d  n = %d (%d mod 4)  tail %s" % (d.s.steps, nd[1], nd[1] % 4, NAME.get(nd[0], nd[0])),
                  flush=True)
        return time.time() - t0 > seconds

    d.run(None, on_event)
    print("stopped at step %d, halted: %s, cycle rules %d" % (d.s.steps, d.s.halt, d.nrules))


def next_from(n, tail, show=False):
    d = Driver(start(tail, n), True)
    out = []
    seen = [None]

    def on_event(d, toks):
        f = fmt(toks, d.s.st)
        if show and not f.startswith('<A> 0011'):
            m = re.search(r'\(110011\)\^(\d+)', f)
            k = m.group(1) if m else None
            if k != seen[0]:
                seen[0] = k
                print(d.ev, re.sub(r'^.*?\(100\)\^\d+ ', '', f, count=1)[:200])
        nd = is_epoch(toks, False)
        if nd is not None and nd[1] > n + 10:
            out.append(nd)
            return True
        return False

    d.run(None, on_event, max_moves=10 ** 8)
    if d.s.halt:
        return "HALT", d.s.steps
    return (out[0][1], out[0][0], d.s.steps) if out else None


def unwind(seed, samples, maxdigits):
    """Tapes  <A> (01110)^40 0111 (100)^30 1111 0011 (100)^60 W 10 111111 00 1111 00 (110011)^4 11  with W a random
    counter word (11100 then digits 100 / 11100): the shape seen in S1 epochs just before the (110011) run out.
    At every event the part right of W's remaining digits is recorded: a finite-state unwinding would give a set of
    such parts that stops growing with the number of digits."""
    random.seed(seed)
    pre = '01110' * 40 + '0111' + '100' * 30 + '1111' + '0011'
    states = collections.Counter()
    ends = collections.Counter()
    for _ in range(samples):
        w = '11100' + ''.join(random.choice(['100', '11100']) for _ in range(random.randint(1, maxdigits)))
        d = Driver(parse('<A> ' + pre + '100' * 60 + w + '10' + '111111' + '00' + '1111' + '00' + '110011' * 4 + '11'),
                   False)
        res = []

        def on_event(d, toks):
            c = ''.join(map(str, cells(d.s.flat()))).rstrip('0')
            m = re.match(r'^(01110)+0111(100)+1111(0011)((100)*)', c)
            if not m:
                return False
            rest = c[m.end():]
            if len(m.group(4)) // 3 < 60 or not rest.startswith('11100'):
                res.append(rest)
                return True
            states[rest[re.match(r'^(11100)((100|11100)*)', rest).end():]] += 1
            return False

        d.run(10 ** 12, on_event, max_moves=3 * 10 ** 6)
        if d.s.halt:
            print("HALT from counter word", w)
            return
        ends[res[0] if res else None] += 1
    print("%d random counter words of up to %d digits: no halt; %d distinct parts right of the counter (longest %d "
          "cells), %d distinct tapes when the counter is used up" % (samples, maxdigits, len(states),
                                                                   max(map(len, states)), len(ends)))


def main(argv):
    cmd = argv[1] if len(argv) > 1 else ""
    if cmd == "classes":
        classes(argv[2] if len(argv) > 2 else None)
    elif cmd == "validate":
        return 0 if validate(argv[2]) else 1
    elif cmd == "run":
        real_run(float(argv[2]))
    elif cmd == "s1":
        print(next_from(int(argv[2]), argv[3] if len(argv) > 3 else TAILS["S1"], show=True))
    elif cmd == "s1map":
        for n in range(int(argv[2]), int(argv[3])):
            r = next_from(n, TAILS["S1"])
            print(n, n % 4, "HALT" if r and r[0] == "HALT" else r and (r[0], r[0] - 8 * n, NAME.get(r[1], r[1])),
                  flush=True)
    elif cmd == "unwind":
        unwind(int(argv[2]), int(argv[3]), int(argv[4]))
    else:
        print(__doc__)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
