"""Write coq/TableCheck.v: for every decided machine, busycoq's TM_from_str "<name>" equals, transition by
transition, the table read by tnf.py. Usage: python3 gen_table_check.py names.txt > coq/TableCheck.v"""
import sys
from tnf import parse, STATES
names = [l.split()[0] for l in open(sys.argv[1]) if l.strip()]
print("From BusyCoq Require Import Individual62.\nRequire Import String.\nOpen Scope string_scope.\n")
for i, n in enumerate(names):
    t = parse(n)
    arms = []
    for q in STATES:
        for b in (0, 1):
            v = t[(q, b)]
            rhs = "None" if v is None else f"Some (S{v[0]}, {v[1]}, {v[2]})"
            arms.append(f"  | ({q}, S{b}) => {rhs}")
    print(f"(* {n} *)")
    print(f"Definition table_{i} (qs : Q * Sym) : option (Sym * dir * Q) :=\n  match qs with\n" + "\n".join(arms) + "\n  end.")
    print(f'Lemma table_ok_{i} : forall q s, TM_from_str "{n}" (q, s) = table_{i} (q, s).\nProof. intros [] []; reflexivity. Qed.\n')
