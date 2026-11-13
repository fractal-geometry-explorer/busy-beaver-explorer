"""Screen of 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1RF for the "few huge blocks + short tail" structure
(the recipe of 1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA), with the accelerated simulator accel.py of this folder.

Event: state B arrives at the left end of the tape.  At events the tape is

    <B> 0 (011)^a 101101 (101011010110)^B junk (U)^C ... tail

(B grows by one word per visit of the left end; U is one of several words of 15, 21, 24 or 30 cells whose block is
eaten; sometimes there is a third big block, a block `1^n`, or a cascade of blocks (10)^k with k doubling).

usage (from the repo root; D = holdouts/1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1RF/py/closure):
  python3 D/screen.py rules MAXSTEPS SECONDS      run from blank tape; list the cycle rules the engine proved (each
                                                  by one symbolic run, counts free) and re-check each on numbers
  python3 D/screen.py cycle ['CFG' [MAXEVENTS]]   from a configuration (default: CYCLE_CFG below), find a period of
                                                  the tape shape with the plain engine and prove it as a rule
  python3 D/screen.py checkpoints AT MAXSTEPS N   compare N events of the accelerated run (up to MAXSTEPS) with the
                                                  plain simulator AT (gcc -O2 -o at holdouts/1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1RF/c/at.c): state,
                                                  head position, tape and step count
  python3 D/screen.py zone RUNFROM [STEPS]        what happens when the clean zone (011)^a runs out: the configuration
                                                  at step 3,368,614,121 (just before a conversion of the left block)
                                                  with a = 8, 7, ..., 0, each run STEPS (default 6e9) plain steps with
                                                  RUNFROM (gcc -O2 -o runfrom holdouts/1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1RF/c/runfrom.c)
"""
import os
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import accel  # noqa: E402
from accel import Driver, bigs, compress, fmt, parse, selftest, shape, verify  # noqa: E402

# a configuration of the real run inside a phase whose tail cycles (see README)
CYCLE_CFG = "<B> 0 (011)^6 001101 (101011010110)^7745 101011010 (101)^4 0 (101101101010101010101011010101)^3061 101101 (10)^8 110 (101)^4 01 (10)^9 (110)^6 10 (101)^4 (01)^4 (10)^4 110110 (101)^4 01 (10)^10 (1)^5 0"


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


def cmd_zone(runfrom, steps):
    target = 3368614121
    d = Driver(None, True)
    got = []

    def on_event(dr, toks):
        if dr.s.steps == target:
            got.append(fmt(toks, dr.s.st))
        return dr.s.steps >= target

    d.run(None, on_event)
    if not got or not got[0].startswith("<B> 0 (011)^8 001101 "):
        print("the run is not at the expected configuration at step", target)
        return 1
    rest = got[0][len("<B> 0 (011)^8 001101 "):]
    print("configuration at step %d: <B> 0 (011)^8 001101 %s ..." % (target, rest[:60]))
    halted = 0
    for a in range(8, -1, -1):
        s = parse("<B> 0 " + ("(011)^%d " % a if a else "") + "001101 " + rest)
        tape = expand(s.flat())
        out = subprocess.run([runfrom, accel.MACHINE, 'B', str(steps)], input=tape + "\n", capture_output=True,
                             text=True).stdout.split()
        if out and out[0] == 'HALT':
            halted += 1
            print("a = %d: HALT" % a, ' '.join(out[1:]))
        else:
            left = out[4][:128] if len(out) > 4 else ''
            k = 0
            while left.startswith('100' * (k + 1)):
                k += 1
            print("a = %d: no halt in %s steps; the tape then begins with (100)^%d%s  %s" % (a, out[1], k,
                  " (or more)" if 3 * k + 3 > len(left) else "", left[3 * k:3 * k + 24]))
    print("halting cases:", halted)
    return 1 if halted else 0


def main(argv):
    if len(argv) >= 4 and argv[1] == 'rules':
        return cmd_rules(float(argv[2]), float(argv[3]))
    if len(argv) >= 2 and argv[1] == 'cycle':
        return cmd_cycle(argv[2] if len(argv) > 2 else CYCLE_CFG, int(argv[3]) if len(argv) > 3 else 3000)
    if len(argv) >= 5 and argv[1] == 'checkpoints':
        return cmd_checkpoints(argv[2], float(argv[3]), int(argv[4]))
    if len(argv) >= 3 and argv[1] == 'zone':
        return cmd_zone(argv[2], int(float(argv[3])) if len(argv) > 3 else 6000000000)
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
