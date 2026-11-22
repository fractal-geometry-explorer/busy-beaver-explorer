"""The walk of lean/Walk.lean (the whole proved table as one map) in Python, read from Walk.lean itself.

A record is (n, m, T) with T = ('long', suffix, t) for `tl t s1/s2/s3` or ('short', code) for the ten short tails.
wstep(w) returns ('go', w'), ('halt',), ('loop',) or ('stuck',), as `wstep` in Walk.lean does.  The rows are parsed
from the `def row_...` bodies, the dispatch from `nearL` and `shortRow`, so this is the Lean map and nothing else.
"""
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
WALK = os.path.join(HERE, "..", "lean", "Walk.lean")
NEED = [4, 1, 4, 3, 2]


def _res(body):
    body = body.strip()
    m = re.fullmatch(r"if N % 2 = 0 then (.*) else (.*)", body)
    if m:
        a, b = _res(m.group(1)), _res(m.group(2))
        return lambda N: a(N) if N % 2 == 0 else b(N)
    if body == ".loop":
        return lambda N: ("loop",)
    if body == ".halt":
        return lambda N: ("halt",)
    m = re.fullmatch(r"\.go \((.*?), (.*?), \.long \.(s\d) (.*)\)", body)
    if m:
        en, em, s, et = (compile(e.replace("/", "//"), "row", "eval") for e in (m.group(1), m.group(2), "0", m.group(4)))
        suf = m.group(3)
        return lambda N: ("go", (eval(en, {"N": N}), eval(em, {"N": N}), ("long", suf, eval(et, {"N": N}))))
    m = re.fullmatch(r"\.go \((.*?), (.*?), \.short \.(\w+)\)", body)
    if m:
        en, em = (compile(e.replace("/", "//"), "row", "eval") for e in (m.group(1), m.group(2)))
        sh = m.group(3)
        return lambda N: ("go", (eval(en, {"N": N}), eval(em, {"N": N}), ("short", sh)))
    raise ValueError(body)


def _load():
    src = open(WALK).read()
    rows = {}
    for m in re.finditer(r"def (row_\w+) \(N : Nat\) : Res :=\n  (.*?)\n\n", src, re.S):
        rows[m.group(1)] = _res(" ".join(m.group(2).split()))
    near, short = {}, {}
    for m in re.finditer(r"\| \.(s\d), (\d+), (\d+), N => (row_\w+) N", src):
        near[(m.group(1), int(m.group(2)), int(m.group(3)))] = rows[m.group(4)]
    for m in re.finditer(r"\| \.(\w+), (\d+), N => (row_\w+) N", src):
        short[(m.group(1), int(m.group(2)))] = rows[m.group(3)]
    return near, short


NEAR, SHORT = _load()


def reset(n, r, t):
    """`reset` of lean/Resets.lean."""
    if r == 0:
        return (10, (n + 5) // 2, t - 4) if t >= 4 else None
    if r == 1:
        return (n + 12, 0, t - 1) if t >= 1 else None
    if r == 2:
        return (n + 32, 0, t - 4) if n >= 1 and t >= 4 else None
    if r == 3:
        return (10, (n + 25) // 2, t - 3) if t >= 3 else None
    if r == 4:
        return (10, (n + 26) // 2, t - 2) if t >= 2 else None
    return None


def wstep(w):
    n, m, T = w
    if m >= 5:
        return ("go", (n + 31 * (m // 5), m % 5, T))
    if T[0] == "long":
        s, t = T[1], T[2]
        if NEED[m] <= t:
            x = reset(n, m, t)
            return ("go", (x[0], x[1], ("long", s, x[2]))) if x else ("stuck",)
        f = NEAR.get((s, m, t))
        return f(n) if f else ("stuck",)
    f = SHORT.get((T[1], m))
    return f(n) if f else ("stuck",)
