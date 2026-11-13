"""Shared by the G11 machines of batch 1: write a machine's `lean/Rules.lean` from a list of rule specifications.

A specification is either
  ("cross", d, S, u, w)    a shift rule: state S crosses n copies of the word w to the right (d = "r", carrying the
                           literal cells u that sit left of the head) or to the left (d = "l", u right of the head);
                           the image word and the step count are found by `bbtools.symtm` and proved by `TM.cross_r` /
                           `TM.cross_l`;
  ("rule", name, start, end, doc)   any symbolic run, proved along the trace (`bbtools.symtm.prove`).

The shift rules are the sweeps the machine makes in its run: they were collected by running the symbolic simulator
from many configurations of the real run, with long periodic stretches written as repeats (see `find_crossings`).

usage (from a machine's folder):  python3 py/rules.py > lean/Rules.lean
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.symtm import Config, prove, rules_file, step, try_cross, try_rotate, STATES  # noqa: E402
from bbtools.machine import Machine  # noqa: E402


def _cells(u):
    return " ".join(str(x) for x in u)


def cross_spec(d, s, u, w):
    """Start and end configurations of a shift rule, the image word left for symtm to find."""
    U = _cells(u)
    if d == "r":
        return f"L {U} {s}> ({w})^n R".replace("  ", " ")
    return f"L ({w})^n {s}> {U} R".replace("  ", " ")


def _cross_image(m, d, s, u, w):
    """Run the shift rule once symbolically to read off the image word v and the steps per copy."""
    c = Config.parse(cross_spec(d, s, u, w))
    x = try_cross(m, c)
    if x is None:
        raise ValueError(f"no shift rule for {d} {s} {u} {w}")
    return "".join(str(b) for b in x.v), x.s


def theorems(machine, specs, prefix):
    m = Machine.parse(machine)
    out = []
    for sp in specs:
        if sp[0] == "cross":
            _, d, s, u, w = sp
            v, k = _cross_image(m, d, s, u, w)
            a = cross_spec(d, s, u, w)
            U = _cells(u)
            b = (f"L ({v})^n {U} {s}> R" if d == "r" else f"L {s}> {U} ({v})^n R").replace("  ", " ")
            name = f"{prefix}_{s}{d}_{w}" + (f"_{''.join(map(str, u))}" if u else "")
            doc = (f"Shift rule: {s} crosses n copies of `{w}` {'rightward' if d == 'r' else 'leftward'}"
                   + (f" carrying `{''.join(map(str, u))}`" if u else "") + f" and leaves `{v}`, {k} steps a copy.")
            out.append(prove(m, name, a, b, doc=doc)[0])
        else:
            _, name, a, b, doc = sp
            out.append(prove(m, name, a, b, doc=doc, count_first=True, max_seg=200)[0])
    return out


def write(machine, ns, specs, prefix, doc):
    sys.stdout.write(rules_file("Machine", ns, theorems(machine, specs, prefix), doc))


def find_crossings(machine, tapes, moves=300):
    """The shift rules met when the symbolic simulator runs `moves` moves from each tape (strings of 0/1 with the
    head cell written I or O, and a state), long periodic stretches compressed into repeats."""
    m = Machine.parse(machine)
    seen = {}
    for st, t in tapes:
        h = t.find("O") if "O" in t else t.find("I")
        T = t.replace("I", "1").replace("O", "0")
        c = Config.parse(f"0^inf {' '.join(_compress(T[:h]))} {st}> {' '.join(_compress(T[h:]))} 0^inf")
        for _ in range(moves):
            try:
                s0 = STATES[c.state]
                x = try_cross(m, c)
                if x is None and try_rotate(c):
                    x = try_cross(m, c)
                if x is None:
                    step(m, c)
                else:
                    seen.setdefault((x.d, s0, x.u, "".join(map(str, x.w))), x.s)
            except Exception:
                break
    return sorted(seen)


def _compress(T):
    out, i = [], 0
    while i < len(T):
        best = None
        for p in range(1, 7):
            w = T[i:i + p]
            if len(w) < p:
                break
            c = 1
            while T[i + c * p:i + (c + 1) * p] == w:
                c += 1
            if c >= 3 and (best is None or c * p > best[1] * len(best[0])):
                best = (w, c)
        if best:
            out.append("(%s)^%d" % best)
            i += len(best[0]) * best[1]
        else:
            out.append(T[i])
            i += 1
    return out
