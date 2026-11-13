#!/usr/bin/env python3
"""The two-block structure of 1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE: check the phase rules along the run, probe the map between two-block tapes, and
list the all-ones tapes from which the machine halts.

usage (from the repo root):
  python3 holdouts/1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE/py/phases.py check [STEPS]   phase rules at every two-block moment of the run (default 10^9;
                                                       needs gcc for tools/c/tmrun.c)
  python3 holdouts/1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE/py/phases.py probe [N]       the next two-block tape from every one with x, y < N (default 60):
                                                       census of parity classes, and every halt
  python3 holdouts/1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE/py/phases.py ones [N]        n <= N (default 200) for which the run from the all-ones tape halts

Tapes: E(x,z) is `E>0 (10)^x 1^z` (head on the 0 at the left end), A(x,y) is `(10)^x 1^y A>0` (head on the blank cell
right of the tape), blank tape around both.
"""
import os
import re
import subprocess
import sys
from collections import Counter

M = "1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE"
FORMS = [
    ("E", r"\|E\|0((?:10)*)(1*)", (2, 1), lambda x, y: ([0] + [1, 0] * x + [1] * y, 0, 4)),
    ("A", r"((?:10)*)(1*)\|A\|0", (2, 1), lambda x, y: ([1, 0] * x + [1] * y + [0], 2 * x + y, 0)),
]          # (name, regex over 'left|S|right' with groups x, y, builder(x, y) -> (cells, head, state))
RULES = {
    "E": (lambda x, z: z >= 2 * x + 8, lambda x, z: ("E", 2 * x + 4, z - 2 * x - 6)),
    "A": (lambda x, y: y % 2 == 0 and 2 * x >= y + 8, lambda x, y: ("A", x - y // 2 - 2, 2 * y + 6)),
}          # name -> (condition(x, y), expected next (name, x, y))
ONES = lambda n: ([1] * n + [0], n, 0)            # builder(n) -> (cells, head, state) of the all-ones tape


def table(m):
    t = {}
    for i, s in enumerate(m.split("_")):
        for b in (0, 1):
            w = s[3 * b:3 * b + 3]
            t[(i, b)] = None if w[0] == "-" else (int(w[0]), 1 if w[1] == "R" else -1, ord(w[2]) - 65)
    return t


T = table(M)


def PARITY(name, x, y):
    """even: E(x,z) with z even >= 2, A(x,y) with x >= 1 and y even; ones: the all-ones tape A(0,y)."""
    if name == "E":
        return "even" if y % 2 == 0 and y >= 2 else ("odd" if y >= 2 else "z<=1")
    if x == 0:
        return "ones"
    return "even" if y % 2 == 0 else "odd"


def raw(tape, pos, st):
    ks = [k for k, v in tape.items() if v] + [pos]
    lo, hi = min(ks), max(ks)
    s = "".join(str(tape.get(i, 0)) for i in range(lo, hi + 1))
    h = pos - lo
    return s[:h] + "|" + "ABCDEF"[st] + "|" + s[h:]


def classify(r):
    for name, rx, wl, _ in FORMS:
        m = re.fullmatch(rx, r)
        if m:
            return name, len(m.group(1)) // wl[0], len(m.group(2)) // wl[1]
    return None


def next_form(cells, pos, st, maxs=10 ** 7):
    """Run from a finite tape until the head extends the tape into a two-block form (or halts)."""
    tape = dict(enumerate(cells))
    lo, hi, k = 0, len(cells) - 1, 0
    while k < maxs:
        tr = T[(st, tape.get(pos, 0))]
        k += 1
        if tr is None:
            return ("halt", k)
        w, d, s = tr
        tape[pos] = w
        pos += d
        st = s
        if pos < lo or pos > hi:
            lo, hi = min(lo, pos), max(hi, pos)
            c = classify(raw(tape, pos, st))
            if c:
                return c + (k,)
    return ("max", k)


def halts_from(cells, pos, st, maxs=10 ** 6):
    tape = dict(enumerate(cells))
    for k in range(1, maxs + 1):
        tr = T[(st, tape.get(pos, 0))]
        if tr is None:
            return k
        w, d, s = tr
        tape[pos] = w
        pos += d
        st = s
    return None


def check(steps):
    here = os.path.dirname(os.path.abspath(__file__))
    repo = os.path.join(here, "..", "..", "..")
    repo = os.environ.get("REPO", repo)
    exe = "/tmp/tmrun_phases"
    if not os.path.exists(exe):
        subprocess.check_call(["gcc", "-O2", "-I", os.path.join(repo, "tools", "c"), "-o", exe,
                               os.path.join(repo, "tools", "c", "tmrun.c")])
    out = subprocess.run([exe, M, str(steps), "records", "100000000"], capture_output=True, text=True).stdout
    ev = []
    for line in out.splitlines():
        p = line.split()
        if p[0] in ("running", "halted"):
            continue
        cells, head, st = "", None, None
        for tok in p[3:]:
            mm = re.match(r"([A-F])>(.*)", tok)
            if mm:
                head, st = len(cells), mm.group(1)
                tok = mm.group(2)
            b, _, n = tok.partition("^")
            cells += b * (int(n) if n else 1)
        tape = {i: int(c) for i, c in enumerate(cells)}
        c = classify(raw(tape, head, ord(st) - 65))
        if c:
            ev.append(c + (int(p[0]),))
    cnt = Counter()
    for a, b in zip(ev, ev[1:]):
        rule = RULES.get(a[0])
        if rule and rule[0](a[1], a[2]):
            exp = rule[1](a[1], a[2])
            cnt[(a[0], "rule holds" if (b[0], b[1], b[2]) == exp else "RULE FAILS")] += 1
        else:
            cnt[(a[0], "other")] += 1
    print(f"{len(ev)} two-block moments in {steps} steps")
    for k, v in sorted(cnt.items()):
        print(f"  {k[0]}: {k[1]}: {v}")
    ones = [e for e in ev if e[0] == 'A' and e[1] == 0]
    print("all-ones moments (n, step):", [(e[2], e[3]) for e in ones])


def probe(n):
    cnt = Counter()
    for name, rx, wl, build in FORMS:
        for x in range(n):
            for y in range(2, n):
                r = next_form(*build(x, y))
                cls = PARITY(name, x, y)
                out = r[0] if r[0] in ("halt", "max") else PARITY(*r[:3])
                cnt[(cls, out)] += 1
    for k, v in sorted(cnt.items()):
        print(f"  {k[0]:>8} -> {k[1]:<8} {v}")


def ones(n):
    print([k for k in range(1, n + 1) if halts_from(*ONES(k))])


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "check"
    arg = int(sys.argv[2]) if len(sys.argv) > 2 else None
    if cmd == "check":
        check(arg or 10 ** 9)
    elif cmd == "probe":
        probe(arg or 60)
    elif cmd == "ones":
        ones(arg or 200)
