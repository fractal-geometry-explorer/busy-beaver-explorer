"""Static scan of Lean files: sorry/admit, new axioms, native_decide (trusts the compiler: Lean.ofReduceBool),
implemented_by/extern/csimp (change what compiled code computes), unsafe, debug.skipKernelTC."""
import re, sys
PATS = {"sorry": r"\bsorry\b|\badmit\b", "axiom": r"^\s*(private\s+)?axiom\b", "native_decide": r"native_decide|Lean\.ofReduceBool|reduceBool",
        "implemented_by/extern/csimp": r"implemented_by|@\[extern|@\[csimp", "unsafe": r"\bunsafe\b",
        "skipKernel": r"skipKernelTC|debug\.skip"}
def strip(s):
    s = re.sub(r"/-.*?-/", "", s, flags=re.S)
    return re.sub(r"--.*", "", s)
for p in sys.argv[1:]:
    src = strip(open(p, errors="replace").read())
    h = {k: len(re.findall(v, src, flags=re.M)) for k, v in PATS.items()}
    print(p, " ".join(f"{k}={v}" for k, v in h.items() if v) or "clean")
