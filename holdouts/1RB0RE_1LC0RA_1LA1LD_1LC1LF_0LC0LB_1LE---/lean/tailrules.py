"""Generate TailRules.lean: the end of a phase of 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE--- for every tail of the
shapes below, proved along the symbolic run (tools/deepmind/dmproof.py `prove_any`: single steps by `rfl`, shift rules
by `TM.cross_r`/`TM.cross_l`).

usage: python3 tailrules.py > TailRules.lean

Notation as in rules.py.  After the rounds of a phase the tape is `0^inf D> 0 1 (10)^k 1^m T` with m = 0, 1 or 2 ones
left over and T the tail.  These rules hold for every tape R right of what they name:

* m = 0, T = `0 1^u R`: `pop`, the first block of the tail joins the ones;
* m = 1: `(10)^k 1 0 = (10)^(k+1)` is a tape identity, so the phase goes on with the next block (Phase.lean);
* m = 2: the tail starts with j blocks of one 1, then
  - a block of t + 3 >= 3 ones: `push2`, two more blocks of one 1 and the block loses 3;
  - an empty block (`0 0`): `zero2`;
  - the end of the tape (j >= 1): `ones2`; j = 0 is `end_e2` of Rules.lean;
  - a last block of two ones: `two2` (j >= 1), `two0` (j = 0).
  The remaining case, a block of two ones with more blocks after it, is not covered (Map.lean).
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "deepmind"))
import dmproof  # noqa: E402
from bbtools.symtm import rules_file  # noqa: E402

M = "1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---"

RULES = [
    ("pop", "0^inf D> 0 1 (10)^k 0 (1)^u R", "0^inf F> 0 (11)^k 1 1 1 1 1 1 1 (1)^u R",
     "No ones left, any tail `0 1^u R`: the first block joins the ones, 2k + 7 + u of them."),
    ("push2", "0^inf D> 0 1 (10)^k 1 1 (01)^j 0 1 1 1 (1)^t R",
     "0^inf F> 0 (11)^k 1 1 1 1 1 1 1 (01)^j 0 1 0 1 0 (1)^t R",
     "Two ones left, the tail starts with j blocks `0 1` and a block of t + 3 ones: 2k + 7 ones, the tail gets two "
     "more blocks `0 1` and the long block loses three ones."),
    ("zero2", "0^inf D> 0 1 (10)^k 1 1 (01)^j 0 0 R", "0^inf F> 0 (11)^k 1 1 1 0 1 1 1 1 1 1 (11)^j R",
     "Two ones left, the tail starts with j blocks `0 1` and an empty block: 2k + 3 ones, and the j blocks become "
     "2j + 6 ones in front of the rest of the tail."),
    ("ones2", "0^inf D> 0 1 (10)^k 1 1 0 1 (01)^j 0^inf", "0^inf F> 0 (11)^k 1 1 1 0 1 1 1 1 1 1 1 1 (11)^j 0^inf",
     "Two ones left and a tail of j + 1 blocks `0 1`: 2k + 3 ones and one block of 2j + 8."),
    ("two2", "0^inf D> 0 1 (10)^k 1 1 0 1 (01)^j 0 1 1 0^inf",
     "0^inf F> 0 1 1 (11)^k 1 0 1 1 1 1 (11)^j 0 1 1 1 1 1 1 0^inf",
     "Two ones left and a tail of j + 1 blocks `0 1` and a last block `0 1 1`: 2k + 3 ones and blocks 2j + 4, 6."),
    ("two0", "0^inf D> 0 1 (10)^k+1 1 1 0 1 1 0^inf", "0^inf F> 0 1 (11)^k+1 0 1 1 1 1 0 1 0 1 0 1 0^inf",
     "Two ones left and the tail `0 1 1`: 2k + 3 ones and blocks 4, 1, 1, 1."),
]


def main():
    ths = [dmproof.prove_any(M, name, a, b, doc)[0] for name, a, b, doc in RULES]
    out = rules_file("Machine", "H103424", ths, f"End-of-phase rules of {M} for whole families of tails, generated "
                     "by `tailrules.py`; do not edit by hand.")
    out = out.replace("namespace H103424", "set_option maxHeartbeats 4000000\n\nnamespace H103424", 1)
    sys.stdout.write(out)


if __name__ == "__main__":
    main()
