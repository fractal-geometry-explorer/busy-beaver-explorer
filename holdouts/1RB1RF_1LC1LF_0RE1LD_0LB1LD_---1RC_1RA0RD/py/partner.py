"""This machine (Y) against its mirror partner 1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE (X), pass by pass.

Mirrored, with D and E swapped, X's table is Y's except that A0 moves left.  Both are compared at Y's pass starts
PS a c = 0^inf B> 0 0 (10)^a 1^c 0^inf.  X's right-end visit T(None, c, a) of its own py/model.py is the mirror image of
PS a c; a visit T(br, c, a) with a bracket has no counterpart.  Y's map is `lean_next` of py/passmap.py (a copy of
the `next` that lean/Phases.lean proves), X's is `step` of X's py/model.py.

usage (from the repository root):
  python3 holdouts/1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD/py/partner.py events PASSES
        odd events of both runs from blank tape (the only places either can halt), side by side
  python3 holdouts/1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD/py/partner.py lag PASSES
        where the two runs part and where X's run is Y's run again, delayed by some passes
  python3 holdouts/1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD/py/partner.py local A_MAX
        pass starts PS a c (a < 30, c < A_MAX) from which one machine halts and the other joins its own blank run
"""
import importlib.util
import os
import sys

HOLD = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))


def _load(name, path):
    s = importlib.util.spec_from_file_location(name, os.path.join(HOLD, path))
    m = importlib.util.module_from_spec(s)
    s.loader.exec_module(m)
    return m


PY = _load("passmap", "1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD/py/passmap.py")
PX = _load("model", "1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE/py/model.py")


def ynext(s):
    """Y: the pass start after PS a c, or 'halt' (c <= 1)."""
    a, c = s
    if c <= 1:
        return "halt"
    q = PY.lean_next(("ps", a, c))
    while q[0] == "q":
        q = PY.lean_next(q)
    return (q[1], q[2])


def xnext(s):
    return PX.step(*s)


def key(x):
    """X's visit as Y's pass start (a, c), or None with a bracket."""
    return (x[2], x[1]) if x[0] is None else None


def events(n):
    y, x, yp, xp = (0, 2), (None, 2, 0), None, None
    for i in range(n):
        if y[1] % 2 and (yp is None or yp[1] % 2 == 0):
            print(f"pass {i:>11}  Y odd stretch from PS 0 {y[1]}")
        if x[1] % 2 and (xp is None or xp[1] % 2 == 0):
            print(f"pass {i:>11}  X odd pool {x[1]}" + (f" behind bracket {x[0]}" if x[0] is not None else ""))
        yp, xp = y, x
        y, x = ynext(y), xnext(x)
        if y == "halt" or x == "halt":
            print("halt at pass", i, y, x)
            return


def lag(n):
    ys, ylist, xlist, y, x = {}, [], [], (0, 2), (None, 2, 0)
    for i in range(n):
        ylist.append(y)
        xlist.append(x)
        ys.setdefault(y, i)
        y, x = ynext(y), xnext(x)
    xs = {}
    for i, x in enumerate(xlist):
        if key(x):
            xs.setdefault(key(x), i)
    prev = None
    for i in range(n):
        k, y = key(xlist[i]), ylist[i]
        if k in ys:
            now = f"X is Y delayed by {i - ys[k]} passes"
        elif y in xs:
            now = f"X is Y delayed by {xs[y] - i} passes"
        else:
            now = "apart"
        if now != prev:
            print(f"pass {i:>8}  {now:<32} Y {y}  X {xlist[i]}")
            prev = now


def local(cmax, n=3000, k=400):
    ys, xs, y, x = {}, {}, (0, 2), (None, 2, 0)
    for i in range(n):
        ys.setdefault(y, i)
        xs.setdefault(x, i)
        y, x = ynext(y), xnext(x)

    def fate(s, nxt, base):
        for j in range(k):
            if s in base:
                return ("joins blank run at pass", base[s], "after", j)
            s = nxt(s)
            if s == "halt":
                return ("halts after", j + 1, "passes")
        return None

    for a in range(30):
        for c in range(2, cmax):
            fy, fx = fate((a, c), ynext, ys), fate((None, c, a), xnext, xs)
            if fy and fx and fy[0] != fx[0]:
                print(f"PS {a} {c}:  Y {' '.join(map(str, fy))};  X {' '.join(map(str, fx))}")


if __name__ == "__main__":
    {"events": events, "lag": lag, "local": local}[sys.argv[1]](int(float(sys.argv[2])))
