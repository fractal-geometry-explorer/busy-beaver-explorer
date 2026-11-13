"""The growth cycle of 1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA as a certificate, its checker, and mutation tests.

Claim (CLAIM below): for every x >= 0 the configuration

    C(r) = <E> 0 (1011001)^59 1011 (0)^5 1101100110110 (011)^16 001101100110 (011)^r 0      with r = 65 + 2x

(state E on the cell left of the tape, the rest blank) reaches C(r + 321042928) after 116,320,154 events and
650373336347246654 + 8765861712 x steps, without halting; and the run from blank tape reaches C(16797709) at step
1,818,198,163,340,705.  So {C(r) : r odd, r >= 65} is a closed set and the machine never halts.

`check(claim)` re-derives the cycle from the claim alone: it builds C(b + 2x) with x a free variable, runs the
symbolic engine of accel.py (which refuses, with Undecided, every operation whose outcome depends on x, proves the
cycle rules it uses for all values of their variables, and applies a rule to a count with a variable only when the
rule's precondition holds for every x), and compares the configuration it returns to, the increment, the number of
events and the step polynomial with the claim.

usage (from the repo root; D = holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/py/closure):
  python3 D/cycle.py check       check the claim (about 20 s)
  python3 D/cycle.py reach       run from blank tape to the first C(r) and compare with the claim (about 15 s)
  python3 D/cycle.py instance    the claim at x = 0, 1 by a numeric run (counts are numbers; about 40 s)
  python3 D/cycle.py mutate      inject defects into the claim, the rules and the machine; each must be reported
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import accel  # noqa: E402
from accel import Driver, Lin, Undecided, bigs, compress, fmt, parse, shape  # noqa: E402

MAX_MOVES = 15000000

CLAIM = dict(
    config="<E> 0 (1011001)^59 1011 (0)^5 1101100110110 (011)^16 001101100110 (011)^%d 0",
    base=65, modulus=2, increment=321042928, events=116320154,
    steps0=650373336347246654, steps1=8765861712,
    reach_r=16797709, reach_steps=1818198163340705, reach_event=6086451,
)


def symbolic_start(claim):
    """C(base + modulus * x) with x the variable 0; the last repeat of the config is the growing one."""
    s = parse(claim["config"] % claim["base"])
    toks = compress(s.flat())
    idx = max(i for i, t in enumerate(toks) if isinstance(t, list))
    assert toks[idx][1] == claim["base"]
    toks[idx] = [toks[idx][0], Lin(claim["base"], {0: claim["modulus"]})]
    h = toks.index('H')
    s.L = toks[:h]
    s.R = list(reversed(toks[h + 1:]))
    s.steps = Lin(0)
    return s, [t if not isinstance(t, list) else [t[0], t[1]] for t in compress(s.flat())], idx


def check(claim, rules=None, log=None):
    """True iff the symbolic run from C(base + m x) returns, at the claimed event, to C(base + increment + m x) with
    the claimed step count.  Returns (ok, reason)."""
    accel.BIG = min(accel.BIG, claim["base"])        # the growing count must count as large
    try:
        s, start, idx = symbolic_start(claim)
    except Exception as e:      # a malformed claim
        return False, "bad claim: %r" % (e,)
    for k in accel.QUERIES:
        accel.QUERIES[k] = None if k == "margin" else 0
    d = Driver(s, True)
    if rules is not None:
        d.rules = rules
    # values of x used only to look for inner cycles (any value will do; rules found are proved for all values)
    d.env = {0: (claim["reach_r"] - claim["base"]) // claim["modulus"]}
    out = {}

    def on_event(d, toks):
        if d.ev < claim["events"]:
            return False
        out["ev"] = d.ev
        out["toks"] = toks
        return True

    try:
        d.run(None, on_event, max_moves=MAX_MOVES)
    except Undecided as e:
        return False, "undecided (the run depends on x): %s" % e
    if d.moves >= MAX_MOVES:
        return False, "no return within %d moves (the true cycle takes 5.4 million)" % MAX_MOVES
    if d.s.halt:
        return False, "the symbolic run halts after %d events" % d.ev
    if out.get("ev") != claim["events"]:
        return False, "no event number %d (a jump passes it)" % claim["events"]
    toks = out["toks"]
    want = [t if not isinstance(t, list) else [t[0], t[1]] for t in start]
    want[idx] = [start[idx][0], Lin(claim["base"] + claim["increment"], {0: claim["modulus"]})]
    if d.s.st != 4 or len(toks) != len(want):
        return False, "other configuration at the end: %s" % fmt(toks, d.s.st)
    for a, b in zip(toks, want):
        same = (a == b) if not isinstance(a, list) or not isinstance(b, list) else (
            a[0] == b[0] and type(a[1]) is type(b[1]) and a[1] == b[1])
        if not same:
            return False, "other configuration at the end: %s" % fmt(toks, d.s.st)
    if claim["increment"] % claim["modulus"] or claim["increment"] <= 0:
        return False, "the increment leaves the family"
    st = d.s.steps
    if not (isinstance(st, Lin) and st.k == claim["steps0"] and st.c == {0: claim["steps1"]}):
        return False, "other step count: %r" % (st,)
    if claim["steps0"] <= 0:
        return False, "empty cycle"
    if log:
        log("  symbolic run: %d moves, %d jumps, %d cycle rules proved on the way" % (d.moves, d.jumps, d.nrules))
        log("  questions about counts with a variable (rule proofs included): %(ge)d comparisons, smallest margin "
            "%(margin)s; %(div)d halvings; %(dec)d decrements" % accel.QUERIES)
        for rs in d.rules.values():
            for r in rs:
                if not accel.selftest(r):
                    return False, "a cycle rule fails its numeric re-check"
    return True, "ok"


def reach(claim):
    """Run from blank tape (cycle rules on) to the first event of the claimed shape."""
    target = shape(compress(parse(claim["config"] % claim["reach_r"]).flat()), 4)
    d = Driver()
    out = {}

    def on_event(d, toks):
        if d.s.steps > 2 * claim["reach_steps"]:
            return True
        if shape(toks, d.s.st) == target:
            out.update(r=bigs(toks)[-1], steps=d.s.steps, ev=d.ev)
            return True
        return False

    d.run(None, on_event)
    ok = (out.get("r") == claim["reach_r"] and out.get("steps") == claim["reach_steps"]
          and out.get("ev") == claim["reach_event"]
          and claim["reach_r"] >= claim["base"] and (claim["reach_r"] - claim["base"]) % claim["modulus"] == 0)
    return ok, out


def instance(claim, x):
    """The claim at one value of x, by a run on numbers (cycle rules on)."""
    r = claim["base"] + claim["modulus"] * x
    d = Driver(parse(claim["config"] % r), True)
    out = {}

    def on_event(d, toks):
        if d.ev >= claim["events"]:
            out.update(ev=d.ev, toks=toks)
            return True
        return False

    d.run(None, on_event)
    want = compress(parse(claim["config"] % (r + claim["increment"])).flat())
    return (not d.s.halt and out.get("ev") == claim["events"] and out["toks"] == want
            and d.s.steps == claim["steps0"] + claim["steps1"] * x)


def mutations():
    """(name, mutated claim or None, patch function or None).  Each must make `check` (or `reach`) fail."""
    c = CLAIM
    out = []
    out.append(("r even (base 64)", dict(c, base=64), None))
    out.append(("left block 58 words", dict(c, config=c["config"].replace("^59", "^58")), None))
    out.append(("left block 61 words", dict(c, config=c["config"].replace("^59", "^61")), None))
    out.append(("inner block 15 words", dict(c, config=c["config"].replace("(011)^16", "(011)^15")), None))
    out.append(("inner block 18 words", dict(c, config=c["config"].replace("(011)^16", "(011)^18")), None))
    out.append(("one cell of the zone flipped", dict(c, config=c["config"].replace("001101100110", "001101100100")),
                None))
    out.append(("increment + 2", dict(c, increment=c["increment"] + 2), None))
    out.append(("increment - 414", dict(c, increment=c["increment"] - 414), None))
    out.append(("one event fewer", dict(c, events=c["events"] - 1), None))
    out.append(("one period of the drain fewer (72 events)", dict(c, events=c["events"] - 72), None))
    out.append(("step count + 1", dict(c, steps0=c["steps0"] + 1), None))
    out.append(("step slope + 2", dict(c, steps1=c["steps1"] + 2), None))
    out.append(("modulus 1 (every r >= 65)", dict(c, modulus=1, steps1=c["steps1"] // 2), None))
    return out


def engine_mutations():
    """Defects in the engine itself; the check of the *true* claim must then fail (or the rule re-check must)."""
    def rule_off_by_one():
        old = accel.verify_mod

        def bad(toks, st, d, k, M):
            r = old(toks, st, d, k, M)
            if r is not None and len(r.D) > 1:
                r.D[1] += 2
            return r
        accel.verify_mod = bad
        return lambda: setattr(accel, "verify_mod", old)

    def rule_low_base():
        old = accel.verify_mod

        def bad(toks, st, d, k, M):
            r = old(toks, st, d, k, M)
            if r is not None:
                r.base = [b % M for b in r.base]        # the rule claimed for all counts of the right parity
            return r
        accel.verify_mod = bad
        return lambda: setattr(accel, "verify_mod", old)

    def machine(flip):
        def f():
            old = dict(accel.T)
            w, m, s = accel.T[flip]
            accel.T[flip] = (1 - w, m, s)
            accel.cacheR.clear()
            accel.cacheL.clear()

            def undo():
                accel.T.clear()
                accel.T.update(old)
                accel.cacheR.clear()
                accel.cacheL.clear()
            return undo
        return f

    return [("rule increments off by 2", rule_off_by_one), ("rules claimed without a lower bound", rule_low_base),
            ("machine: B1 writes 0", machine((1, 1))), ("machine: E1 writes 0", machine((4, 1)))]


def main(argv):
    cmd = argv[1] if len(argv) > 1 else "check"
    if cmd == "check":
        ok, why = check(CLAIM, log=print)
        print("claim:", "CHECKED" if ok else "FAILED: " + why)
        return 0 if ok else 1
    if cmd == "reach":
        ok, out = reach(CLAIM)
        print("from blank tape:", out, "OK" if ok else "MISMATCH")
        return 0 if ok else 1
    if cmd == "instance":
        bad = 0
        for x in (0, 1, 7):
            ok = instance(CLAIM, x)
            print("x = %d (r = %d): %s" % (x, CLAIM["base"] + 2 * x, "OK" if ok else "MISMATCH"))
            bad += not ok
        return 1 if bad else 0
    if cmd == "mutate":
        missed = 0
        for name, claim, _ in mutations():
            big = accel.BIG
            ok, why = check(claim)
            accel.BIG = big
            print("%-45s %s" % (name, "NOT REPORTED" if ok else "reported: " + why[:110]), flush=True)
            missed += ok
        for name, patch in engine_mutations():
            undo = patch()
            try:
                ok, why = check(CLAIM, log=lambda *_: None)
            except Exception as e:      # a broken engine may also crash; that is a report
                ok, why = False, "exception %r" % (e,)
            undo()
            print("%-45s %s" % (name, "NOT REPORTED" if ok else "reported: " + why[:110]), flush=True)
            missed += ok
        ok, why = check(CLAIM)
        print("%-45s %s" % ("(no defect)", "passes" if ok else "FAILS: " + why))
        print("defects not reported:", missed)
        return 1 if missed or not ok else 0
    print(__doc__)
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
