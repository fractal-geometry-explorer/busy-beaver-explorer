"""Validation of the closed set of py/closure/cert.json (see closure.py).

usage (from the repo root; D = holdouts/1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA/py/closure):
  python3 D/validate.py real SECONDS        the rounds of the real run (numeric engine) against their classes: next
                                            tail, next B = k + c x and the step polynomial, for every round
  python3 D/validate.py plain ROUND [N]     N classes (spread over the certificate) at x = 0 and x = 1 against the
                                            plain bit-level simulator c/round.c (ROUND: its compiled binary)
  python3 D/validate.py mutate [cert|engine|engine2]   inject defects into the certificate and the engine; each must be reported
  python3 D/validate.py neighbours [SEC [STRIDE]]   classes outside the closed set: other residues of B for the 62 tails
  python3 D/validate.py tails [SEC [STRIDE]]   the same for tails not in the set (one block of a tail one pair
                                            longer or shorter), B = 1 mod 3
"""
import json
import os
import subprocess
import sys
import time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import accel  # noqa: E402
import closure  # noqa: E402
from accel import Lin, Pol  # noqa: E402

CERT = os.path.join(HERE, "cert.json")


def load():
    return json.load(open(CERT))


def find(cert, tail, B):
    for c in cert["classes"]:
        if c["tail"] == tail and B % c["m"] == c["r"] and B >= c["r0"]:
            return c
    return None


def steps_at(c, x):
    return Pol([Fraction(a) for a in c["steps"]]).at(x)


def real(seconds):
    cert = load()
    nodes = [n for n in closure.real_nodes(seconds=seconds) if n[3] >= cert["thr"]]
    bad = 0
    used = set()
    for (e0, s0, t0, B0), (e1, s1, t1, B1) in zip(nodes, nodes[1:]):
        c = find(cert, t0, B0)
        if c is None:
            print("round from B = %d: in no class" % B0)
            bad += 1
            continue
        used.add((c["tail"], c["r"], c["m"]))
        x = (B0 - c["r0"]) // c["m"]
        if (c["to"], c["k"] + c["c"] * x, steps_at(c, x)) != (t1, B1, s1 - s0):
            print("round from B = %d: prediction differs" % B0)
            bad += 1
    print("rounds compared: %d (B up to %d digits), classes used: %d of %d, tails seen: %d, mismatches: %d"
          % (len(nodes) - 1, len(str(nodes[-1][3])), len(used), len(cert["classes"]),
             len(set(n[2] for n in nodes)), bad))
    return bad


def plain(binary, n):
    cert = load()
    cl = cert["classes"]
    pre = cert["prefix"]
    bad = 0
    for c in cl[::max(1, len(cl) // n)][:n]:
        for x in (0, 1):
            B = c["r0"] + c["m"] * x
            st = steps_at(c, x)
            inp = "A\n" + pre + "01" * B + c["tail"] + "\n"
            out = subprocess.run([binary, accel.MACHINE, str(st)], input=inp, capture_output=True, text=True).stdout
            want = pre + "01" * (c["k"] + c["c"] * x) + c["to"]
            f = out.split()
            ok = (len(f) == 4 and f[0] == "A" and f[3] == want.strip("0")
                  and int(f[1]) == int(f[2]) - want.index("1"))
            # no earlier arrival: the engine's round is the first node event, and the step count is exact
            print("tail %s.. B = %d (mod %d), %d steps: %s" % (c["tail"][:24], B, c["m"], st, "OK" if ok else "MISMATCH"),
                  flush=True)
            bad += not ok
    return bad


def mutate(what="all"):
    cert = load()
    cl = cert["classes"]
    sample = set(range(0, len(cl), 80))
    missed = 0

    def report(name, ok, bad):
        nonlocal missed
        print("%-58s %s" % (name, "NOT REPORTED" if ok else "reported: " + bad[0][:90]), flush=True)
        missed += ok

    def with_class(i, **kw):
        c2 = json.loads(json.dumps(cert))
        c2["classes"][i].update(kw)
        return c2
    i = 7
    c = cl[i]
    muts = [
        ("successor count k + 3", with_class(i, k=c["k"] + 3)),
        ("successor count k + its own modulus", with_class(i, k=c["k"] + c["c"])),
        ("successor slope c + 3", with_class(i, c=c["c"] + 3)),
        ("successor slope 2 c", with_class(i, c=2 * c["c"])),
        ("one cell of the successor tail flipped", with_class(i, to=c["to"][:9] + str(1 - int(c["to"][9])) + c["to"][10:])),
        ("step count + 1", with_class(i, steps=[str(int(c["steps"][0]) + 1)] + c["steps"][1:])),
        ("class claimed for modulus 3 (all residues)", with_class(i, m=3, r=c["r"] % 3)),
        ("class residue + 3", with_class(i, r=(c["r"] + 3) % c["m"])),
    ]
    c2 = json.loads(json.dumps(cert))
    del c2["classes"][i]
    muts.append(("one class removed", c2))
    c2 = json.loads(json.dumps(cert))
    c2["classes"] = [x for x in c2["classes"] if x["tail"] != cl[400]["tail"]]
    muts.append(("one tail removed", c2))
    c2 = json.loads(json.dumps(cert))
    c2["start"]["B"] += 3
    muts.append(("start node B + 3", c2))
    c2 = json.loads(json.dumps(cert))
    c2["thr"] = 60000
    muts.append(("threshold 60000 (successors below it)", c2))
    for name, m in (muts if what in ("all", "cert") else []):
        ok, bad = closure.check(m, log=None, rerun={i}, reach=True)
        report("certificate: " + name, ok, bad)

    def patched(obj, attr, new):
        old = getattr(obj, attr)
        setattr(obj, attr, new(old))
        return lambda: setattr(obj, attr, old)

    def rule_D(old):
        def bad(toks, st, d, k, M):
            r = old(toks, st, d, k, M)
            if r is not None and len(r.D) > 1:
                r.D[1] += 3
            return r
        return bad

    def rule_base(old):
        def bad(toks, st, d, k, M):
            r = old(toks, st, d, k, M)
            if r is not None:
                r.base = [b % M for b in r.base]
            return r
        return bad

    def apps(delta, nosplit=False):
        def mk(old):
            def bad(rule, counts):
                if nosplit:
                    for n, D in zip(counts, rule.D):
                        if isinstance(n, Lin) and D < 0 and any(a % (-D) for a in n.c.values()):
                            n.c = {v: a - a % (-D) + (-D) for v, a in n.c.items()}     # pretend it divides
                N = old(rule, counts)
                if isinstance(N, Lin):
                    return N.k if delta is None else N + delta
                return N
            return bad
        return mk

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

    eng = [
        ("cycle rule increments off by 3", lambda: patched(accel, "verify_mod", rule_D)),
        ("cycle rules claimed without a lower bound", lambda: patched(accel, "verify_mod", rule_base)),
        # (+1 or -1 application is not a defect: the rules hold below their stated lower bound, and a missing
        # application is made up by a numeric one; both give the true result.)
        ("symbolic number of applications + 6", lambda: patched(accel, "applications", apps(6))),
        ("symbolic number of applications: variable part dropped", lambda: patched(accel, "applications", apps(None))),
        ("divisibility of the class modulus not asked for", lambda: patched(accel, "applications", apps(0, True))),
        ("machine: C1 writes 1", machine((2, 1))),
        ("machine: E0 writes 0", machine((4, 0))),
        ("machine: F0 writes 1", machine((5, 0))),
    ]
    if what == "engine2":       # a class claimed for too coarse a modulus, with the engine not asking for divisibility
        cert = with_class(i, m=3, r=c["r"] % 3)
        sample = {i}
        eng = eng[4:5]
    else:                       # on the true certificate that defect changes nothing (every modulus fits)
        del eng[4]
    for name, patch in (eng if what != "cert" else []):
        undo = patch()
        try:
            ok, bad = closure.check(cert, log=None, rerun=sample, reach=False, max_moves=300000)
        except Exception as e:      # a broken engine may also crash; that is a report
            ok, bad = False, ["exception %r" % (e,)]
        undo()
        report("engine: " + name, ok, bad)
    cert = load()
    ok, bad = closure.check(cert, log=None, rerun=sample, reach=True)
    print("%-58s %s" % ("(no defect; %d classes re-run)" % len(sample), "passes" if ok else "FAILS: " + bad[0]))
    print("defects not reported:", missed)
    return 1 if missed or not ok else 0


def neighbours(seconds, stride=1, tails=False):
    """For every tail of the closed set, the residues of B that are not in the set (at the tail's modulus; split
    further when the engine asks for it).  stride: take every stride-th such residue."""
    cert = load()
    index = {}
    for c in cert["classes"]:
        index.setdefault(c["tail"], []).append((c["r"], c["m"]))
    rules = {}
    t0 = time.time()
    cnt = {}
    halting = []
    work = []
    for tail, cl in sorted(index.items()):
        m = cl[0][1]
        have = set(r for r, _ in cl)
        work.extend((tail, r, m) for r in range(m) if r not in have)
    work = work[::stride]
    if tails:
        # other tails: one pair `10` removed from, or added to, one block of a tail of the set; B = 1 mod 3
        seen = set(index)
        work = []
        for tail in sorted(index):
            p = tail.find("1010")
            while p >= 0:
                q = p
                while tail[q:q + 2] == "10":
                    q += 2
                for t2 in (tail[:p] + tail[p + 2:], tail[:p] + "10" + tail[p:]):
                    if t2 not in seen:
                        seen.add(t2)
                        work.append((t2, 1, 3))
                p = tail.find("1010", q)
        work = work[::stride]
    tried = 0
    while work and time.time() - t0 < seconds:
        tail, r, m = work.pop()
        res = closure.run_class(tail, r, m, rules, max_moves=400000)
        kind = res["kind"]
        if kind == "split":
            m2 = closure.lcm(m, res["d"])
            if m2 <= 20000:
                work.extend((tail, (r + m * j) % m2, m2) for j in range(m2 // m))
                continue
            kind = "not followed (modulus > 20000)"
        tried += 1
        if kind == "node":
            kind = "next node is in the closed set" if closure.covered(index, res["to"], res["k"], res["c"],
                                                                       cert["thr"]) else "next node is outside the set"
        if kind == "halt":
            halting.append((tail, r, m, res["steps"]))
        if kind == "undecided":
            kind += ": " + res["why"][:60]
        cnt[kind] = cnt.get(kind, 0) + 1
    print("classes outside the closed set decided: %d (%.0f s; %d left untried)" % (tried, time.time() - t0, len(work)))
    for k, v in sorted(cnt.items()):
        print("  %-50s %d" % (k, v))
    for tail, r, m, st in halting[:12]:
        print("  HALTS for every B = %d mod %d, B >= %d: tail %s, steps %s" % (r, m, cert["thr"], tail, st))
    return 0


def main(argv):
    cmd = argv[1] if len(argv) > 1 else ""
    if cmd == "real":
        return 1 if real(float(argv[2])) else 0
    if cmd == "plain":
        return 1 if plain(argv[2], int(argv[3]) if len(argv) > 3 else 6) else 0
    if cmd == "mutate":
        return mutate(argv[2] if len(argv) > 2 else "all")
    if cmd == "neighbours":
        return neighbours(float(argv[2]) if len(argv) > 2 else 400, int(argv[3]) if len(argv) > 3 else 1)
    if cmd == "tails":
        return neighbours(float(argv[2]) if len(argv) > 2 else 400, int(argv[3]) if len(argv) > 3 else 1, True)
    print(__doc__)
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
