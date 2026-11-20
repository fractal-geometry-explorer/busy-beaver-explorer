"""Write lean/Bound.lean for a machine of the block-list family: the run-length simulator of tools/lean/TM/RLE.lean
with the proved closed-form visit (`visit_closed` of the machine's Family.lean) as a jump, so that a long run from
blank tape without a halt is one evaluation (`bound_of_run`).  Template: py/bound_generic.lean.

usage: python3 gen_bound_lean.py MACHINE NAMESPACE START > lean/Bound.lean   (START: the frame-A start state)
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def file_text(machine, ns, st):
    with open(os.path.join(HERE, "bound_generic.lean")) as f:
        s = f.read()
    return s.replace("@MACHINE@", machine).replace("@NS@", ns).replace("@START@", st)


if __name__ == "__main__":
    sys.stdout.write(file_text(*sys.argv[1:4]))
