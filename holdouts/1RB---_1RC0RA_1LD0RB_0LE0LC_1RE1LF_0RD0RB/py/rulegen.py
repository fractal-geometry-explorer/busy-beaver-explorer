"""Shared helpers of the G01 list machines (used by the six folders of this worker; see each README).

* `sym(machine, start, stop=None)`: symbolic run of `bbtools.symtm` from a configuration string until the head touches
  a context, a count would need a case split, or `stop(cfg)`; with carried words up to 8 cells (the library default
  is 3), which the sweeps of these machines need.
* `write_rules(machine, ns, rules, path, doc)`: a Lean file of rules, each proved by `symtm.prove` (rfl steps, shift
  rules, omega for the count).  `rules` is a list of (name, start, end, doc); `end` must be the configuration as the
  run writes it (re-bracketing allowed, see symtm).
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(REPO, "tools", "py"))

import bbtools.symtm as S  # noqa: E402
from bbtools.machine import Machine, STATES  # noqa: E402

S.MAX_CARRY = 8


def sym(machine, start, stop=None, max_moves=200000, rotate=True):
    m = Machine.parse(machine) if isinstance(machine, str) else machine
    c = S.Config.parse(start)
    try:
        S.run(m, c, stop or (lambda c: False), max_moves=max_moves, rotate=rotate)
        res = "stop"
    except S.TouchContext as e:
        res = f"context {e}"
    except S.NeedSplit as e:
        res = f"split {e}"
    except S.Halted as e:
        res = f"HALT {e}"
    except RuntimeError:
        res = "max"
    c.left, c.right = S.canon(c.left), S.canon(c.right)
    return res, c


def at_end(side, state, sym_=None):
    """stop(cfg): the head, in `state` (and reading `sym_` if given), with only blank tape on `side` ('L' or 'R')."""
    q = STATES.index(state)

    def f(c):
        if c.steps.is_zero() or c.state != q:
            return False
        other = c.left if side == "L" else c.right
        if not all(isinstance(t, S.Blank) or t == 0 for t in other):
            return False
        return sym_ is None or (c.right and c.right[0] == sym_)
    return f


def write_rules(machine, ns, rules, path, doc, max_seg=40, rotate=True):
    """ns None: the namespace of the Machine.lean next to `path`."""
    if ns is None:
        import re
        with open(os.path.join(os.path.dirname(path), "Machine.lean")) as f:
            ns = re.search(r"^namespace (\S+)", f.read(), re.M).group(1)
    thms = []
    for name, start, end, d in rules:
        text, _ = S.prove(machine, name, start, end, doc=d, rotate=rotate, count_first=True, max_seg=max_seg)
        thms.append(text)
    head = f"import Machine\n\n/-! {doc} -/\n\nnamespace {ns}\n\nopen TM\n\n"
    with open(path, "w") as f:
        f.write(head + "\n".join(thms) + f"\nend {ns}\n")
    return len(thms)


def chain(machine, start, stop, k):
    """Up to k consecutive stops from `start`: a list of (start, end, steps) strings, each end the next start."""
    out = []
    cur = start
    for _ in range(k):
        res, c = sym(machine, cur, stop)
        if res != "stop":
            break
        out.append((cur, repr(c), str(c.steps)))
        cur = repr(c)
    return out


def _at_context(c):
    """The head is next to a context on one side (the step after it would read the context)."""
    if c.steps.is_zero():
        return False
    return any(len(side) == 1 and isinstance(side[0], S.Ctx) for side in (c.left, c.right))


def shift_rules(machine, starts):
    """(name, start, end, doc) for each (name, start, doc): the run from `start` until the head reaches the context."""
    out = []
    for name, start, d in starts:
        res, c = sym(machine, start, _at_context, rotate=False)
        assert res == "stop", (name, res, c)
        out.append((name, start, repr(c), d + f" ({c.steps} steps)"))
    return out


def main_shifts(here, machine, starts, doc):
    """Write ../lean/Rules.lean of the folder of `here` (a gen_rules.py) from shift rules; print them."""
    rs = shift_rules(machine, starts)
    for name, s, e, d in rs:
        print(name, ":", s, "->", e, "|", d)
    n = write_rules(machine, None, rs, os.path.join(os.path.dirname(os.path.abspath(here)), "..", "lean", "Rules.lean"),
                    doc, rotate=False)
    print(n, "theorems")
