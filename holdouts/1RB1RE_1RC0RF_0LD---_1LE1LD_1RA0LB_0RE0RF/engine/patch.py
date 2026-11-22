"""Make the engine of busycoq PR 93 run the table W = 1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB0LF (PR 93's T3 with its halt F1
replaced by 0LF, which is what T3's E1 does).
usage: python3 patch.py engine93.v WC.v      (engine93.v: the output of tools/coq/t4engine/strip.py on PR 93's file)
Only the source table changes: every macro rule of PR 93 is a rule of T3 that never reaches F1, so it is a rule of W.
The finite denotation and starts of tools/coq/t4engine/extra.v are appended, as for the T4 engine."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
T4 = os.path.join(HERE, "..", "..", "..", "tools", "coq", "t4engine")
src = open(sys.argv[1]).read()
old = '(TM_from_str "1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB---").\n'
assert src.count(old) == 1
src = src.replace(old, '(TM_from_str "1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB0LF").\n'
                  'Local Notation "c -->* c\'" := (c -[ src_tm ]->* c\') (at level 40).\n')
p = open(os.path.join(T4, "patch.py")).read()
hdr = p.split("hdr='''")[1].split("'''")[0]
inf = 'Local Infix "/" := Nat.div : nat_scope.\nLocal Infix "mod" := Nat.modulo (at level 40, no associativity) : nat_scope.\n'
extra = open(os.path.join(T4, "extra.v")).read()
open(sys.argv[2], "w").write(hdr + "\nModule T4C.\n" + inf + src + "\n" + extra + "\nEnd T4C.\n")
