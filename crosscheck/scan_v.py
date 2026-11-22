"""Static scan of Coq files for anything that could weaken a proof: admitted goals, axioms, disabled checkers,
native_compute (trusts the OCaml compiler), and redefinitions of busycoq's halts/c0/TM_from_str/step."""
import re, sys
PATS = {
    "Admitted": r"\bAdmitted\b", "admit": r"\badmit\b", "Axiom/Parameter/Conjecture": r"^\s*(Local\s+)?(Axiom|Axioms|Parameter|Parameters|Conjecture)\b",
    "Hypothesis/Variable": r"^\s*(Hypothesis|Hypotheses|Variable|Variables|Context)\b",
    "unset-checking": r"Unset\s+(Guard|Universe|Positivity)\s+Checking|bypass_check",
    "native_compute": r"native_compute|native_cast_no_check", "vm_cast_no_check": r"vm_cast_no_check",
    "redefines-core": r"^\s*(Definition|Fixpoint|Inductive|Notation|Let)\s+\"?(halts|halts_in|c0|tape0|TM_from_str|step|halted|TM)\b\"?",
    "Extraction": r"\bExtract\b",
}
def strip_comments(s):
    out, depth, i = [], 0, 0
    while i < len(s):
        if s.startswith("(*", i): depth += 1; i += 2
        elif s.startswith("*)", i) and depth: depth -= 1; i += 2
        else:
            if depth == 0: out.append(s[i])
            i += 1
    return "".join(out)
for path in sys.argv[1:]:
    src = strip_comments(open(path, errors="replace").read())
    hits = {k: len(re.findall(p, src, flags=re.M)) for k, p in PATS.items()}
    print(path.split("/")[-1], " ".join(f"{k}={v}" for k, v in hits.items() if v) or "clean")
