"""Rewrite ../lean/EngineRules.lean: busycoq PR 93's macro rules on this machine, proved by bbtools.symtm.

Exchange the names E and F and replace the detour D0 = 1LE, E0 = 0RA, A1 = 1RA by one step 1RA (it ends in the same
configuration unless the cell left of D is 1, where the machine halts): the table becomes
1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB1RF_0RA---, which is T4 = 1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0RA--- (the table of
the T4 engine, tools/coq/t4engine, retargeted from DeepMind's busycoq PR 93) except E1: T4 erases the 1 and steps
left (0LF, then F0 = 0RA), this machine keeps it and steps right (1RF, then F0 = 0RA with F always on the 0 that D
has just written).  PR 93's engine works with CfgR l r = l A> 0100 r, CfgL l r = l <B 1 r and
CfgJ l r = l <C 100 r and the digit words D n = 1 (11)^n 00 and S n = 1 (01)^(n+1).  A rule that ends in CfgL or
CfgJ (head on the last cell of L) is stated one step before, when the head is still on the first cell of the rule's
own tape: CfgL L r is one step after `L C> 1 r` and CfgJ L r is one step after `L B> 0 0 0 r`.

Rules that change: PR 93's collision, finishP and defect0 rules no longer return to the left: at the E1 step the head
turns right and runs into the tape beyond the rule (collision below).  Only collide (defect0D with the digit D 0)
stays local.

usage: python3 holdouts/MACHINE/py/engine_rules.py   (from the repository root; then lean/check.sh)
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools import symtm  # noqa: E402
from bbtools.machine import Machine  # noqa: E402

M = "1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE"
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
    ("left", Ls("(10)^n+1", "1", ""), Le(D("n")), "PR 93 `rule_left`: CfgL (L · S n) R reaches CfgL L (D n · R). Same as T3 and T4."),
    ("even", R("", "(11)^n+1 0 0"), Le(D("n+1") + " 1 0"), "PR 93 `rule_even`: CfgR L ((11)^(n+1) 00 R) reaches CfgL L (D (n+1) · 10 · R). Same as T3 and T4."),
    ("leftJ", Js("(10)^n+1", "1", ""), Le(D("n+1")), "PR 93 `rule_leftJ`: CfgJ (L · S n) R reaches CfgL L (D (n+1) · R). Same as T3 and T4."),
    ("defect1", R("", "1 0 " + D(1) + " 1 (11)^m 0"), Le(D(0) + " " + D(0) + " " + D("m+1") + " 1"), "PR 93 `rule_defect1`: CfgR L (10 · D 1 · 1 (11)^m 0 · R) reaches CfgL L (D 0 · D 0 · D (m+1) · 1 · R). Same as T3 and T4."),
    ("dblank0", R("", "1 0 " + D(0) + " 0 0"), R("1 0 1 1 0 0 1", ""), "PR 93 `rule_defect_blank0`: CfgR L (10 · D 0 · 00 · R) reaches CfgR (L · S 0 · 1001) R. Same as T3 and T4."),
    ("collision", Ls("1 0 1 1 0", "0", ""), "L 1 0 1 0 1 1 1 A> R", "Changed. PR 93 `rule_collision`: CfgL (L · 001101) R reaches CfgJ L (1111 · R) for T3 and CfgL L (111111 · R) for T4; here the head turns right and reaches R in state A, with 1010111 written before it."),
    ("collisionD", Ls("1 0 1 1 0", "0", D("n")), "L 1 0 1 0 1 1 1 1 (11)^n A> 0 0 R", "Changed. PR 93 `rule_collisionD`, with the digit D n after the collision: the head runs on in A over the digit's 1s to its 00 (T3: CfgJ L (D (n+2) · R), T4: CfgL L (D (n+3) · R))."),
    ("collide", R("", "1 0 " + D(0) + " " + D(0)), Le(D(1) + " " + D(1) + " 1"), "Changed but still local. PR 93 `rule_collide`: CfgR L (10 · D 0 · D 0 · R) reaches CfgJ L (D 2 · 10 · R) for T3 and CfgL L (D 3 · 10 · R) for T4; here CfgL L (D 1 · D 1 · 1 · R)."),
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
