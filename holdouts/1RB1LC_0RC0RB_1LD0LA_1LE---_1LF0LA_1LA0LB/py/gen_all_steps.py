"""Write lean/Steps_<state>.lean: the step theorems of every family in fams.py (gen_fam.py), with their passes, one
file per reading state (the letter in the family's name).

usage: python3 gen_all_steps.py    (writes ../lean/Steps_*.lean)
"""
import os, sys
import gen_fam as GF, fams, symglue as G

HERE = os.path.dirname(os.path.abspath(__file__))
files = {}
n = 0
def parse_runs(d):
    return [(b == "1", G.S.parse_lin(c)) for b, c in (p.split(":") for p in d.split(","))]


for fam in fams.FAMS:
    name, suf, hi, d = fam[:4]
    runs = parse_runs(d)
    xs = dict(start=parse_runs(fam[4][0]), end=parse_runs(fam[4][1]), s0=2) if len(fam) > 4 else None
    st = name.split("_")[1]
    for (nm, spec, pt, thm, info) in GF.generate_all(name, suf, hi, runs, log=lambda m: print("  ", m, file=sys.stderr), xs=xs):
        print(nm, spec[3], info, file=sys.stderr)
        files.setdefault(st, []).extend(pt + [thm, ""])
        n += 1
for st, body in files.items():
    with open(os.path.join(HERE, "..", "lean", f"Steps_{st}.lean"), "w") as f:
        f.write("\n".join([GF.HEAD] + body + ["end H49767", ""]))
print(f"{n} step theorems in {len(files)} files", file=sys.stderr)
