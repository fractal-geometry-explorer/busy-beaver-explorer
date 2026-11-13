"""Lean files for the machines of worker batch g11-b2: shift rules proved by `bbtools.symtm`, and concrete
configurations that halt (or reach a configuration) checked by evaluation of the list simulator.

usage (from the repository root):
  python3 holdouts/1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD/py/leanfiles.py MACHINE NAMESPACE rules.json OUTDIR

rules.json: {"rules": [[name, start, end, doc], ...],
             "halts": [[name, left_cells_nearest_first, right_cells, state, doc], ...]}
Writes OUTDIR/Rules.lean (if rules) and OUTDIR/Shapes.lean (if halts).
"""
import json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.symtm import prove, rules_file          # noqa: E402
from bbtools.machine import Machine                  # noqa: E402


def lbool(cells):
    return "[" + ", ".join("true" if c == "1" else "false" for c in cells) + "]"


def fsim(m, left, right, state, limit=10**7):
    """The list simulator of tools/lean/TM/Fin.lean (fstep), exactly: returns (n, final left, right, state) at the
    first configuration whose transition halts."""
    tr = m.split("_")
    l, r, q, n = [int(c) for c in left], [int(c) for c in right], state, 0
    while n < limit:
        x = r[0] if r else 0
        t = tr["ABCDEF".index(q)][3 * x:3 * x + 3]
        if t[2] == "-":
            return n, l, r, q
        w, d, q = int(t[0]), t[1], t[2]
        if d == "R":
            l, r = [w] + l, r[1:]
        else:
            r = [l[0] if l else 0, w] + r[1:]
            l = l[1:]
        n += 1
    return None


def main(m, ns, spec, out):
    spec = json.load(open(spec))
    if spec.get("rules"):
        ths = []
        for name, s, e, doc in spec["rules"]:
            txt, _ = prove(m, name, s, e, doc=doc)
            ths.append(txt)
        open(os.path.join(out, "Rules.lean"), "w").write(rules_file(
            "Machine", ns, ths, f"# Shift rules of {m}\n\nProved from symbolic traces by `bbtools.symtm.prove` "
            "(written by `py/leanfiles.py`); each holds for every value of the counts and every tape in the contexts."))
    if spec.get("halts"):
        lines = ["import Machine", "", f"/-! # Configurations of {m} that halt",
                 "", "Each is a finite configuration (cells listed nearest the head first) whose run is evaluated on the",
                 "list simulator of `tools/lean/TM/Fin.lean`; written by `py/leanfiles.py`. -/", "",
                 f"namespace {ns}", "", "open TM", ""]
        for name, left, right, state, doc in spec["halts"]:
            n, l2, r2, q2 = fsim(m, left, right, state)
            c = f"(⟨{lbool(left)}, {lbool(right)}, .{state}⟩ : FCfg St)"
            d = f"(⟨{lbool(''.join(map(str, l2)))}, {lbool(''.join(map(str, r2)))}, .{q2}⟩ : FCfg St)"
            lines += [f"/-- {doc} It halts after {n} steps. -/",
                      f"theorem {name} : Halts trans (FCfg.toCfg {c}) := by",
                      f"  have h1 : TM.fsteps trans {n} {c} = some {d} := by decide +kernel",
                      f"  have h2 : TM.fstep trans {d} = none := by decide +kernel",
                      f"  exact ⟨{n}, _, by rw [FCfg.steps_eq, h1]; rfl, by rw [FCfg.step_eq, h2]; rfl⟩", ""]
        lines += [f"end {ns}", ""]
        open(os.path.join(out, "Shapes.lean"), "w").write("\n".join(lines))


if __name__ == "__main__":
    main(*sys.argv[1:5])
