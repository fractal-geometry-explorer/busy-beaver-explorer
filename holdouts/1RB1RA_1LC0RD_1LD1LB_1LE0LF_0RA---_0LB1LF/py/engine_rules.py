"""Rewrite ../lean/EngineRules.lean: busycoq PR 93's macro rules, as they hold for this machine, proved by bbtools.symtm.

Exchange the names E and F and replace the detour D0 = 1LE, E0 = 0RA, A1 = 1RA by one step 1RA (it ends in the same
configuration unless the cell left of D is 1, where the machine halts): the table becomes
1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB1LE, which is the table T3 of DeepMind's proof in busycoq PR 93
(1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB---) except E1 (T3: 0LF then F0 = 0LB; here 1LE).  PR 93's engine works with
CfgR l r = l A> 0100 r, CfgL l r = l <B 1 r and CfgJ l r = l <C 100 r, the digit words D n = 1 (11)^n 00 and
S n = 1 (01)^(n+1) (written on the left, so read backwards there).  The rules below are stated for this machine, with
its detours, for every count and every tape L, R around them.  A rule that ends in CfgL or CfgJ (head on the last cell
of L) is stated one step before, when the head is still on the first cell of the rule's own tape:
CfgL L r is one step after `L C> 1 r` and CfgJ L r is one step after `L B> 0 0 0 r`.

Rules that change: the four rules of PR 93 that end in CfgJ (collision, collide, defect0, finishP) still end in CfgJ,
but where T3 writes the digit D (k+1) first, this machine writes D k 1 0.

usage: python3 holdouts/MACHINE/py/engine_rules.py   (from the repository root; then lean/check.sh)
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools import symtm  # noqa: E402
from bbtools.machine import Machine  # noqa: E402

M = "1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF"
symtm.MAX_CARRY = 8


def S(n):  # S n on the left, in tape order
    return f"(10)^{n}+1 1"


def D(n):
    return f"1 (11)^{n} 0 0"


def R(l, r):  # CfgR
    return f"L {l} A> 0 1 0 0 {r} R"


def Ls(lw, last, r):  # CfgL (L lw last) r: head on the last cell of the left word
    return f"L {lw} B> {last} 1 {r} R"


def Le(r):  # one step before CfgL L r
    return f"L C> 1 {r} R"


def Js(lw, last, r):  # CfgJ (L lw last) r
    return f"L {lw} C> {last} 1 0 0 {r} R"


def Je(r):  # one step before CfgJ L r
    return f"L B> 0 0 0 {r} R"


RULES = [
    ("left", Ls("(10)^n+1", "1", ""), Le(D("n")), "PR 93 `rule_left`: CfgL (L · S n) R reaches CfgL L (D n · R). Same as T3."),
    ("even", R("", "(11)^n+1 0 0"), Le(D("n+1") + " 1 0"), "PR 93 `rule_even`: CfgR L ((11)^(n+1) 00 R) reaches CfgL L (D (n+1) · 10 · R). Same as T3."),
    ("leftJ", Js("(10)^n+1", "1", ""), Le(D("n+1")), "PR 93 `rule_leftJ`: CfgJ (L · S n) R reaches CfgL L (D (n+1) · R). Same as T3."),
    ("turnJ", Js("1 1 1 (01)^b 0", "1", ""), R("(01)^b+2", ""), "PR 93 `rule_turnJ` (b+1 for its b): CfgJ (L · 111 · (10)^(b+1)) R reaches CfgR (L · (10)^(b+2)) R. Same as T3."),
    ("defect1", R("", "1 0 " + D(1) + " 1 (11)^m 0"), Le(D(0) + " " + D(0) + " " + D("m+1") + " 1"), "PR 93 `rule_defect1`: CfgR L (10 · D 1 · 1 (11)^m 0 · R) reaches CfgL L (D 0 · D 0 · D (m+1) · 1 · R). Same as T3."),
    ("dblank0", R("", "1 0 " + D(0) + " 0 0"), R("1 0 1 1 0 0 1", ""), "PR 93 `rule_defect_blank0`: CfgR L (10 · D 0 · 00 · R) reaches CfgR (L · S 0 · 1001) R. Same as T3."),
    ("collisionD", Ls("1 0 1 1 0", "0", D("n")), Je(D("n+1") + " 1 0"), "Changed. PR 93 `rule_collisionD`: CfgL (L · 001101) (D n · R) reaches CfgJ L (D (n+2) · R) for T3; here CfgJ L (D (n+1) · 10 · R)."),
    ("collide", R("", "1 0 " + D(0) + " " + D(0)), Je(D(1) + " 1 0 1 0"), "Changed. PR 93 `rule_collide`: CfgR L (10 · D 0 · D 0 · R) reaches CfgJ L (D 2 · 10 · R) for T3; here CfgJ L (D 1 · 10 · 10 · R)."),
    ("defect0D", R("", "1 0 " + D(0) + " " + D("m")), Je(D("m+1") + " 1 0 1 0"), "Changed. PR 93 `rule_defect0D`: CfgR L (10 · D 0 · D m · R) reaches CfgJ L (D (m+2) · 10 · R) for T3; here CfgJ L (D (m+1) · 10 · 10 · R)."),
    ("defect0", R("", "1 0 " + D(0) + " 1 (11)^m 0"), Je(D("m+1") + " 1 0 1"), "Changed. PR 93 `rule_defect0`: CfgR L (10 · D 0 · 1 (11)^m 0 · R) reaches CfgJ L (1111 · D m · 1 · R) = CfgJ L (D (m+2) · 1 · R) for T3; here CfgJ L (D (m+1) · 101 · R)."),
    ("finishP", Ls("1 0 1 1 0 (01)^b 0", "1", ""), Je(D("b") + " 1 0"), "Changed. PR 93 `rule_finishP`: CfgL (L · S 0 · 01 · (10)^(b+1)) R reaches CfgJ L (D (b+1) · R) for T3; here CfgJ L (D b · 10 · R)."),
]


def main():
    m = Machine.parse(M)
    th = []
    for name, start, end, doc in RULES:
        th.append(symtm.prove(m, "pr93_" + name, start, end, doc=doc, rotate=True, count_first=True, max_seg=40)[0])
    lean = os.path.join(HERE, "..", "lean")
    ns = re.search(r"namespace (\w+)", open(os.path.join(lean, "Machine.lean")).read()).group(1)
    doc = (f"# {M}: busycoq PR 93's macro rules on this machine\n\n" + __doc__.split("\n\nusage")[0].split("\n", 1)[1].strip()
           + "\n\nWritten by the folder's `py/engine_rules.py` with `tools/py/bbtools/symtm.py`; do not edit by hand.")
    with open(os.path.join(lean, "EngineRules.lean"), "w") as f:
        f.write(symtm.rules_file("Machine", ns, th, doc))


if __name__ == "__main__":
    main()
