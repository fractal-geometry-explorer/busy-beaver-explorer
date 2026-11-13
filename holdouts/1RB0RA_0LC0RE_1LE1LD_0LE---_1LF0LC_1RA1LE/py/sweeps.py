"""Write lean/Sweeps.lean for a machine: the sweep rules of its self-loops, proved by `bbtools.symtm.prove`.

A self-loop `q y -> w d q` makes the head cross any run `y^n` in state q, leaving `w^n` behind: for a right move
`L q> y^n R` reaches `L w^n q> R` in n steps, for a left move `L x y^n q> y R` (x the other symbol)
reaches `L q> x w^(n+1) R` in n+1 steps.  These are the shift rules the macro descriptions in README.md use.

usage (from the repository root): python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/sweeps.py M
"""
import os
import re
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "tools", "py"))
from bbtools.machine import Machine, STATES  # noqa: E402
from bbtools.symtm import prove, rules_file  # noqa: E402


def main(m):
    d = os.path.join(ROOT, "holdouts", m, "lean")
    ns = re.search(r"^namespace (\w+)", open(os.path.join(d, "Machine.lean")).read(), re.M).group(1)
    mm = Machine.parse(m)
    ths, names = [], []
    for s in range(mm.n):
        for y in (0, 1):
            t = mm.table[s][y]
            if t is None or t[2] != s:
                continue
            w, mv, _ = t
            q = STATES[s]
            name = f"sweep_{q}{y}"
            if mv == 1:
                start, end = f"L {q}> {y}^n R", f"L {w}^n {q}> R"
            else:
                x = 1 - y
                start, end = f"L {x} {y}^n {q}> {y} R", f"L {q}> {x} {w}^n+1 R"
            doc = f"`{q}` crosses a run of {y}s {'rightwards' if mv == 1 else 'leftwards'}, writing {w}s."
            try:
                txt, _ = prove(m, name, start, end, doc=doc)
            except Exception as e:  # noqa: BLE001
                print("skip", name, e)
                continue
            ths.append(txt)
            names.append(name)
    open(os.path.join(d, "Sweeps.lean"), "w").write(
        rules_file("Machine", ns, ths, "Sweep rules of the self-loops, written by `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/sweeps.py`."))
    print(" ".join(names))


if __name__ == "__main__":
    main(sys.argv[1])
