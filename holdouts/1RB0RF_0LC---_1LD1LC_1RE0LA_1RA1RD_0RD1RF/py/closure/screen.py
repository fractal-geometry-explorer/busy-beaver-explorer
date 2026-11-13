"""Screen of 1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1RF for the "few huge blocks + short tail" structure
(the recipe of 1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA), with the accelerated simulator accel.py of this folder.

Event: state A arrives at the left end of the tape.  At events the tape is

    <A> 0 (011)^a 101101 (101011010110)^B junk (U)^C ... tail

(B grows by one word per visit of the left end; U is one of several words of 15, 21, 24 or 30 cells whose block is
eaten; sometimes there is a third big block, a block `1^n`, or a cascade of blocks (10)^k with k doubling).

usage (from the repo root; D = holdouts/1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1RF/py/closure):
  python3 D/screen.py rules MAXSTEPS SECONDS      run from blank tape; list the cycle rules the engine proved (each
                                                  by one symbolic run, counts free) and re-check each on numbers
  python3 D/screen.py cycle ['CFG' [MAXEVENTS]]   from a configuration (default: CYCLE_CFG below), find a period of
                                                  the tape shape with the plain engine and prove it as a rule
  python3 D/screen.py checkpoints AT MAXSTEPS N   compare N events of the accelerated run (up to MAXSTEPS) with the
                                                  plain simulator AT (gcc -O2 -o at holdouts/1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1RF/c/at.c): state,
                                                  head position, tape and step count
"""
import os
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import accel  # noqa: E402
from accel import Driver, bigs, compress, fmt, parse, selftest, shape, verify  # noqa: E402

# a configuration of the real run inside a phase whose tail cycles (see README)
CYCLE_CFG = "<A> 0 (011)^170 101101 (101011010110)^2150 10101 (10)^4 11011010110 (101010101101101)^792 1010 (101)^4 0101101101010110101 (10)^5 1 (10)^4 1101101010110110 (101)^7 010 (101)^4 01101101101011010100110110101 (10)^10 (1)^8 0"


def cmd_rules(maxsteps, seconds):
    d = Driver(None, True)
    t0 = time.time()
    d.run(maxsteps, lambda dr, toks: time.time() - t0 > seconds)
    s = d.s
    print("HALT" if s.halt else "END (no halt)", "steps", s.steps, "events", d.ev, "engine moves", d.moves,
          "jumps", d.jumps, "rules", d.nrules, "rule attempts that failed", d.nfail)
    rules = [r for rs in d.rules.values() for r in rs]
    bad = 0
    for r in rules:
        ok = selftest(r)
        bad += not ok
        print("rule: %d events, modulus %d, base %s, counts change by %s, used %d times, numeric re-check %s"
              % (r.events, r.M, r.base, r.D, r.uses, "pass" if ok else "FAIL"))
        sh = r.shape
        print("   shape:", fmt([list(t) if isinstance(t, tuple) else t for t in sh[1:]], sh[0]).replace('^-1', '^n'))
    print("TAPE", fmt(compress(s.flat()), s.st))
    print("rules: %d, numeric re-check failed: %d" % (len(rules), bad))
    return 1 if bad or s.halt else 0


def cmd_cycle(cfg, maxev):
    s = parse(cfg)
    d = Driver(s, False)
    hist = []
    found = [None]

    def on_event(dr, toks):
        hist.append((hash(shape(toks, dr.s.st)), tuple(bigs(toks))))
        n = len(hist)
        for k in range(1, (n - 1) // 2 + 1):
            a, b, c = hist[n - 1 - 2 * k], hist[n - 1 - k], hist[n - 1]
            if a[0] == b[0] == c[0] and len(a[1]) == len(b[1]) == len(c[1]):
                d1 = [y - x for x, y in zip(a[1], b[1])]
                if d1 == [y - x for x, y in zip(b[1], c[1])] and any(x < 0 for x in d1):
                    found[0] = (k, d1, toks)
                    return True
        return n >= maxev

    d.run(None, on_event)
    if not found[0]:
        print("no cycle in %d events" % len(hist))
        return 1
    k, dd, toks = found[0]
    print("shape period %d events; counts %s change by %s" % (k, bigs(toks), dd))
    print("at:", fmt(toks, s.st))
    r = verify(toks, s.st, dd, k)
    if r is None:
        print("NOT PROVED")
        return 1
    print("PROVED for all x >= 0: %d events, counts %s + %d x_i change by %s, steps %r"
          % (r.events, r.base, r.M, r.D, r.S))
    ok = selftest(r)
    print("numeric re-check with the plain engine (x in 0, 1, 3 and mixes):", "pass" if ok else "FAIL")
    return 0 if ok else 1


def expand(toks):
    out = []
    for t in toks:
        if t == 'H':
            continue
        if isinstance(t, list):
            out.extend(t[0] * t[1])
        else:
            out.append(t)
    return ''.join(map(str, out))


def cmd_checkpoints(at, maxsteps, n):
    d = Driver(None, True)
    pick = []

    def on_event(dr, toks):
        if dr.s.steps >= maxsteps * (len(pick) + 1) / n and len(pick) < n:   # first event after each threshold
            flat = dr.s.flat()
            pick.append((dr.s.steps, dr.s.st, flat.index('H'), expand(compress(flat)), dr.jumps))
        return len(pick) >= n

    d.run(None, on_event)
    out = subprocess.run([at, accel.MACHINE] + [str(e[0]) for e in pick], capture_output=True, text=True).stdout
    good = 0
    for line, e in zip(out.splitlines(), pick):
        f = line.split()
        ok = (len(f) == 4 and int(f[0]) == e[0] and f[1] == 'ABCDEF'[e[1]]
              and f[3][int(f[2]):].rstrip('0') == e[3].rstrip('0') and '1' not in f[3][:int(f[2])] and e[2] == 0)
        good += ok
        print(e[0], "match" if ok else "DIFFERENT", "(tape %d cells, %d jumps so far)" % (len(f[3]), e[4])
              if len(f) == 4 else line[:60])
    print("checkpoints: %d of %d agree (state, head, tape, step count)" % (good, len(pick)))
    return 0 if good == len(pick) and pick else 1


def main(argv):
    if len(argv) >= 4 and argv[1] == 'rules':
        return cmd_rules(float(argv[2]), float(argv[3]))
    if len(argv) >= 2 and argv[1] == 'cycle':
        return cmd_cycle(argv[2] if len(argv) > 2 else CYCLE_CFG, int(argv[3]) if len(argv) > 3 else 3000)
    if len(argv) >= 5 and argv[1] == 'checkpoints':
        return cmd_checkpoints(argv[2], float(argv[3]), int(argv[4]))
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
