"""Writes lean/Sweeps.lean: the sample-to-sample rules of 1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---, each for a
carry chain of ANY length (a list `ts` of digits in shape S3, proved by induction on the list with
`tools/py/bbtools/seqtm.py` and `lean/Seq.lean`).

Sample point: C on a 0 at the right end of the tape, `... (100)^last 1 0 1 C> 0^inf`.  The tape is a sea of the
word 100 with walls, the digits of a base-4 counter (lowest digit next to the head):

    S0 = 1000   S1 = 110   S2 = 10000   S3 = 1010          (S = 10 at the left end and after some mergers)

A digit is `(100)^r W` (r = its left run).  One sweep adds one to the counter: the head crosses the carry chain
(the S3 digits next to the end), changes the first other digit (the *stop*: S0 -> S1, S1 -> S2 with its left run
one shorter, S2 -> S3) and returns, turning every S3 into S0; the last run grows by one.  When every digit is S3
(the counter is full), the head goes to the left end: every S3 becomes S0 and a new digit S1 is born at the right
end (`overflow`).  Each theorem is one such rule for every value of the runs, every list ts and every tape L beyond
the stop.  The end configuration is written the way the run writes it (re-bracketed); the README gives each rule in
digit form.

usage: python3 py/sweeps.py > lean/Sweeps.lean
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools import seqtm, symtm  # noqa: E402
from bbtools.machine import Machine, STATES  # noqa: E402

M = "1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---"
NS = "H159355"
CHAIN = "[ (100)^c 1 0 0 1 0 1 0 ]^ts"        # the carry chain: digits S3 with left runs c+1
END = "(100)^z 1 0 0 1 0 1 C> 0^inf"           # the last run (100)^(z+1), then 101, head C on a 0
RULES = [
    ("sweep_s0", f"L (100)^a 1 0 0 1 0 0 0 {CHAIN} {END}",
     "Stop digit S0 (left run a+1): it becomes S1; every S3 of the chain becomes S0; the last run grows by one."),
    ("sweep_s1", f"L (100)^a 1 0 0 1 1 0 {CHAIN} {END}",
     "Stop digit S1 (left run a+1): it becomes S2 with left run a; every S3 of the chain becomes S0."),
    ("sweep_s2", f"L (100)^a 1 0 0 1 0 0 0 0 {CHAIN} {END}",
     "Stop digit S2 (left run a+1): it becomes S3; every S3 of the chain becomes S0."),
    ("merge_s_s1", f"L (100)^a 1 0 0 1 0 1 1 0 {CHAIN} {END}",
     "A merger: stop digit S1 with left run 0 right after S = 10 (left run a+1): the two become one S0 (left run "
     "a+1), one digit fewer."),
    ("merge_s3_s1", f"L (100)^a 1 0 0 1 0 1 0 1 1 0 {CHAIN} {END}",
     "A merger: stop digit S1 with left run 0 right after S3 (left run a+1): they become S (left run a+1) and S0 "
     "(left run 0)."),
    ("overflow", f"0^inf 1 0 {CHAIN} {END}",
     "The overflow: 0^inf 10 followed only by S3 digits (the counter is full): the head crosses the whole tape, "
     "every S3 becomes S0 and a new digit S1 is born at the right end, with the old last run as its left run "
     "and a new last run of 1."),
    ("left_s_s1", f"0^inf 1 0 1 1 0 {CHAIN} {END}",
     "The first block used up: 0^inf 10 110 (S, then S1 with left run 0) becomes 0^inf 1000: the leading 10 and the "
     "S1 merge into an S0 at the left end."),
    ("merge_s2_s1", f"L (100)^a 1 0 0 1 0 0 0 0 1 1 0 {CHAIN} {END}",
     "A merger: stop digit S1 with left run 0 right after S2 (left run a+1): the two become one wall X6 = 1000000 "
     "(left run a+1)."),
    ("sweep_x6", f"L (100)^a 1 0 0 1 0 0 0 0 0 0 {CHAIN} {END}",
     "Stop digit X6 (left run a+1): it becomes S0 (same run) followed by S = 10 with left run 0."),
    ("sweep_x5", f"L (100)^a 1 0 0 1 0 0 0 0 0 {CHAIN} {END}",
     "Stop digit X5 = 100000 (left run a+1): it becomes S with left run a+2."),
    ("left_s0", f"0^inf 1 0 0 0 {CHAIN} {END}",
     "Left end, first digit S0 with left run 0 as the stop: it becomes S1."),
    ("left_s1", f"0^inf 1 1 0 {CHAIN} {END}",
     "Left end, first digit S1 with left run 0 as the stop: it vanishes (its cells join the first run of the chain)."),
    ("left_s2", f"0^inf 1 0 0 0 0 {CHAIN} {END}",
     "Left end, first digit S2 with left run 0 as the stop: it becomes S3."),
    ("left_s3", f"0^inf 1 0 1 0 {CHAIN} {END}",
     "Left end, first digit S3 with left run 0 and only S3 after it: it becomes S [0] S0 (an overflow without a "
     "new digit at the right end)."),
    ("left_s_s0", f"0^inf 1 0 1 0 0 0 {CHAIN} {END}",
     "Left end [0]S [0]S0 with the S0 as the stop: the S0 becomes S1."),
    ("left_s_s2", f"0^inf 1 0 1 0 0 0 0 {CHAIN} {END}",
     "Left end [0]S [0]S2 with the S2 as the stop: the tape becomes [0]S3 [0]S."),
    ("left_s3_s", f"0^inf 1 0 1 0 1 0 {CHAIN} {END}",
     "Left end [0]S3 [0]S (= [0]S [0]S3) followed only by S3 digits: an overflow; the left end becomes [0]S [0]S0, "
     "every S3 becomes S0 and a new S1 is born at the right end."),
]


def sample(c):
    if c.steps.is_zero() or c.state != STATES.index("C"):
        return False
    r = symtm.canon(c.right)
    return r == [symtm.Blank()] or r == [0, symtm.Blank()]


def main():
    m = Machine.parse(M)
    ths = []
    for name, start, doc in RULES:
        txt, fin, _ = seqtm.prove(m, name, seqtm.parse(start), sample, doc=doc)
        ths.append(txt)
    head = (f"import Seq\n\n/-! # {M}: the sample-to-sample rules, for carry chains of any length\n\n"
            "Generated by `py/sweeps.py` with `tools/py/bbtools/seqtm.py`; do not edit by hand.  Each theorem is one "
            "sweep (from the head at the right end in state C on a 0 to the next time it is there), for every value "
            "of the variables, every list `ts` (the carry chain: the S3 digits next to the end, any number of them) "
            "and every tape `L` beyond.  Kernel only. -/\n\nset_option maxRecDepth 100000\n"
            "set_option maxHeartbeats 10000000\n\n"
            f"namespace {NS}\n\nopen TM\n\n")
    sys.stdout.write(head + "\n".join(ths) + f"\nend {NS}\n")


if __name__ == "__main__":
    main()
