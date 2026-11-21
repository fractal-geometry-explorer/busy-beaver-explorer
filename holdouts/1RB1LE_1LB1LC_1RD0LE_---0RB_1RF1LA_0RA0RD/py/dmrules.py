"""Generate lean/DMRules.lean: the tape rules behind DeepMind's halts-iff map of 1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD,
each proved along a symbolic run (tools/py/bbtools/symtm.py, with the near-side rotations of tools/deepmind/dmproof.py).

usage: python3 py/dmrules.py > lean/DMRules.lean      (from holdouts/1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD)

E(q, a, b, c) is `0^inf E> 0 0^q 1^a 0 1^b 0 1^c 0^inf` and F(d, a, b, c) is `0^inf 1^(d+1) F> 1^a 0 1^b 0 1^c 0^inf`.
One rule per case of DeepMind's `next` (and of its dispatch functions `enterF_*`), split by the parities that decide
the next state; `(11)^j` is a block of even length.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "deepmind"))
import dmproof  # noqa: E402
from bbtools.machine import Machine  # noqa: E402
from bbtools.symtm import Config, rules_file  # noqa: E402

M = "1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD"
NS = "H25239"

def blk(x): return x if x else ""
def E(q, A, B, C):
    return " ".join(w for w in ["0^inf E> 0", "0" if q else "", A, "0", B, "0", C, "0^inf"] if w)
def F(D, A, B, C):
    return " ".join(w for w in ["0^inf", D, "1 F>", A, "0", B, "0", C, "0^inf"] if w)
ODD = "(11)^j 1"; EVEN = "(11)^j"
R = []
def r(name, a, b, doc): R.append((name, a, b, doc))
r("blank_E", "0^inf A> 0^inf", "0^inf E> 0 0 1 1 1 0 0 0^inf", "From blank tape to E(1, 3, 0, 0).")
# E false a b c
r("e0_even", E(0, "(11)^k", "(1)^b", "(1)^c"), F("", "(11)^k", "(1)^b", "(1)^c"), "E(0, 2k, b, c) to F(0, 2k, b, c).")
r("e0_1", E(0, "1", "(1)^b", "(1)^c"), "halt", "E(0, 1, b, c) halts.")
r("e0_3e", E(0, "1 1 1", "(11)^j", "(1)^c"), E(0, "(11)^j 1 1", "(1)^c 1 1 1", ""), "E(0, 3, 2j, c) to E(0, 2j + 2, c + 3, 0).")
r("e0_3o", E(0, "1 1 1", "(11)^j 1", "(1)^c"), E(1, "(11)^j 1 1 1", "(1)^c 1 1 1", ""), "E(0, 3, 2j + 1, c) to E(1, 2j + 3, c + 3, 0).")
r("e0_5", E(0, "1 1 1 1 1 (11)^k", "(1)^b", "(1)^c"), "0^inf 1 1 0 D> 0 (11)^k 1 0 (1)^b 1 1 1 0 (1)^c 0^inf", "E(0, 2k + 5, b, c) halts: D reads 0.")
# E true
r("e1_000", E(1, "", "", ""), "halt", "E(1, 0, 0, 0) halts.")
r("e1_00ce", E(1, "", "", "(11)^j 1"), E(0, "(11)^j 1 1", "1 1 1", ""), "E(1, 0, 0, 2j + 1) to E(0, 2j + 2, 3, 0).")
r("e1_00co", E(1, "", "", "(11)^j 1 1"), E(1, "(11)^j 1 1 1", "1 1 1", ""), "E(1, 0, 0, 2j + 2) to E(1, 2j + 3, 3, 0).")
r("e1_0b_even", E(1, "", "(11)^k 1 1", "(1)^c"), F("1 1", "(11)^k 1 1", "(1)^c", ""), "E(1, 0, 2k + 2, c) to F(2, 2k + 2, c, 0).")
r("e1_0b_1", E(1, "", "1", "(1)^c"), "halt", "E(1, 0, 1, c) halts.")
r("e1_0b_3e", E(1, "", "1 1 1", "(11)^j"), E(0, "(11)^j 1 1 1 1", "1 1 1", ""), "E(1, 0, 3, 2j) to E(0, 2j + 4, 3, 0).")
r("e1_0b_3o", E(1, "", "1 1 1", "(11)^j 1"), E(1, "(11)^j 1 1 1 1 1", "1 1 1", ""), "E(1, 0, 3, 2j + 1) to E(1, 2j + 5, 3, 0).")
r("e1_0b_5", E(1, "", "(11)^k 1 1 1 1 1", "(1)^c"), E(1, "1 1 1", "(11)^k 1", "(1)^c 1 1 1"), "E(1, 0, 2k + 5, c) to E(1, 3, 2k + 1, c + 3).")
r("e1_a_even", E(1, "(11)^k 1 1", "(1)^b", "(1)^c"), F("1", "(11)^k 1 1", "(1)^b", "(1)^c"), "E(1, 2k + 2, b, c) to F(1, 2k + 2, b, c).")
r("e1_a_1", E(1, "1", "(1)^b", "(1)^c"), "halt", "E(1, 1, b, c) halts.")
r("e1_a_3e", E(1, "1 1 1", "(11)^j", "(1)^c"), E(1, "(11)^j 1 1 1", "(1)^c 1 1 1", ""), "E(1, 3, 2j, c) to E(1, 2j + 3, c + 3, 0).")
r("e1_a_3o", E(1, "1 1 1", "(11)^j 1", "(1)^c"), E(0, "(11)^j 1 1 1 1", "(1)^c 1 1 1", ""), "E(1, 3, 2j + 1, c) to E(0, 2j + 4, c + 3, 0).")
r("e1_a_5", E(1, "(11)^k 1 1 1 1 1", "(1)^b", "(1)^c"), E(1, "(11)^k 1 1 1", "(1)^b 1 1 1 1 1 1", "(1)^c"), "E(1, 2k + 5, b, c) to E(1, 2k + 3, b + 6, c).")
# F_even d 0 ..
r("f_000e", F("(11)^j", "", "", ""), E(1, "(11)^j 1", "1 1 1", ""), "F(2j, 0, 0, 0) to E(1, 2j + 1, 3, 0).")
r("f_000o", F("(11)^j 1", "", "", ""), E(0, "(11)^j 1 1", "1 1 1", ""), "F(2j + 1, 0, 0, 0) to E(0, 2j + 2, 3, 0).")
r("f_00c", F("(1)^d", "", "", "(1)^c 1"), F("(1)^d 1", "", "(1)^c 1", ""), "F(d, 0, 0, c + 1) to F(d + 1, 0, c + 1, 0).")
r("f_0b_even", F("(1)^d", "", "(11)^k 1 1", "(1)^c"), F("(1)^d 1", "(11)^k 1 1", "(1)^c", ""), "F(d, 0, 2k + 2, c) to F(d + 1, 2k + 2, c, 0).")
r("f_0b_1", F("(1)^d", "", "1", "(1)^c"), "halt", "F(d, 0, 1, c) halts.")
for dp in (0, 1):
    for cp in (0, 1):
        D = "(11)^i" + (" 1" if dp else ""); Cc = "(11)^j" + (" 1" if cp else "")
        m = (dp + 1 + cp + 2) % 2   # parity of d + 1 + c + 2
        ones = "(11)^i (11)^j" + " 1" * (dp + cp + 3)
        r(f"f_0b_3_{dp}{cp}", F(D, "", "1 1 1", Cc), E(m, ones, "1 1 1", ""), f"F(d, 0, 3, c), d = 2i + {dp}, c = 2j + {cp}, to E(d + c + 3, 3, 0).")
r("f_0b_5e", F("(11)^i", "", "(11)^k 1 1 1 1 1", "(1)^c"), E(0, "(11)^i 1 1", "(11)^k 1", "(1)^c 1 1 1"), "F(2i, 0, 2k + 5, c) to E(0, 2i + 2, 2k + 1, c + 3).")
r("f_0b_5o", F("(11)^i 1", "", "(11)^k 1 1 1 1 1", "(1)^c"), E(1, "(11)^i 1 1 1", "(11)^k 1", "(1)^c 1 1 1"), "F(2i + 1, 0, 2k + 5, c) to E(1, 2i + 3, 2k + 1, c + 3).")
r("f0_2e", F("", "1 1", "(11)^j", "(1)^c"), E(0, "(11)^j 1 1", "(1)^c 1 1 1", ""), "F(0, 2, 2j, c) to E(0, 2j + 2, c + 3, 0).")
r("f0_2o", F("", "1 1", "(11)^j 1", "(1)^c"), E(1, "(11)^j 1 1 1", "(1)^c 1 1 1", ""), "F(0, 2, 2j + 1, c) to E(1, 2j + 3, c + 3, 0).")
r("f1_2", F("1", "1 1", "(1)^b", "(1)^c"), E(1, "(1)^b 1 1 1 1", "(1)^c", ""), "F(1, 2, b, c) to E(1, b + 4, c, 0).")
r("fd_2e", F("(11)^i 1 1", "1 1", "(1)^b", "(1)^c"), E(1, "(11)^i 1", "(1)^b 1 1 1 1", "(1)^c"), "F(2i + 2, 2, b, c) to E(1, 2i + 1, b + 4, c).")
r("fd_2o", F("(11)^i 1 1 1", "1 1", "(1)^b", "(1)^c"), E(0, "(11)^i 1 1", "(1)^b 1 1 1 1", "(1)^c"), "F(2i + 3, 2, b, c) to E(0, 2i + 2, b + 4, c).")
r("f_k2z", F("(1)^d", "1 1 1 1", "(1)^b", "(1)^c"), F("(1)^d 1", "", "(1)^b 1 1 1", "(1)^c"), "F(d, 4, b, c) to F(d + 1, 0, b + 3, c).")
r("f_k2", F("(1)^d", "1 1 1 1 1 1 (11)^k", "(1)^b", "(1)^c"), F("(1)^d 1", "(11)^k 1 1", "(1)^b 1 1 1", "(1)^c"), "F(d, 2k + 6, b, c) to F(d + 1, 2k + 2, b + 3, c).")


def main():
    m = Machine.parse(M)
    ths = []
    for name, a, b, doc in R:
        if b == "halt":
            b = str(dmproof.before_halt(m, Config.parse(a)))
        ths.append(dmproof.prove_any(M, name, a, b, doc)[0])
    sys.stdout.write(rules_file("Machine", NS, ths, f"Rules of {M} for DeepMind's map, generated by "
                                "`py/dmrules.py`; do not edit by hand."))


if __name__ == "__main__":
    main()
