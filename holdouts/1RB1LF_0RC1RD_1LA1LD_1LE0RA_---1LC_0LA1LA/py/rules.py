"""Generate lean/Rules.lean: the rounds of 1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA, proved along the symbolic run
(tools/py/bbtools/symtm.py: single steps by `rfl`, shift rules by `TM.cross_r` / `TM.cross_l`).

usage: python3 rules.py > ../lean/Rules.lean

A round starts with the head in state A on the blank cell left of the tape `1^x1 0 1^x2 0 ... 0 1^xk` and ends the
next-but-one time the head is there in state A (or, for the transitions marked `count 3/4`, after a few more visits;
see the README).  `(11)^n` is n copies of `11`.  Each rule is stated as the symbolic run writes its end; Rounds.lean
restates them on block lengths.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.machine import Machine  # noqa: E402
from bbtools.symtm import Blank, Config, STATES, prove, rules_file, run  # noqa: E402

M = "1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA"


def K(*bl):
    return "0^inf A> 0 " + " 0 ".join(bl) + " 0^inf"


def run_to(start, count):
    """The symbolic run from `start` to the `count`-th later time the head is at the left end in state A."""
    m = Machine.parse(M)
    cfg = Config.parse(start)
    left, first = [count], [True]

    def stop(c):
        if first[0]:
            first[0] = False
            return False
        if c.state == STATES.index("A") and len(c.left) == 1 and isinstance(c.left[0], Blank):
            left[0] -= 1
            return left[0] == 0
        return False

    run(m, cfg, stop, max_moves=200000, rotate=True)
    return cfg


# (name, start blocks, visits of the left end, doc)
RULES = [
    ("e0", ["(11)^x+3", "(11)^y+4"], 2, "Two even blocks: a block `9` is split off the right one, which loses 4."),
    ("e9", ["(11)^x+3", "(11)^y+2", "1^9"], 2, "`9` becomes `7` and a new block `6` is appended."),
    ("e7", ["(11)^x+3", "(11)^y+2", "1^7", "(11)^z"], 2, "`7` becomes `5`, the last block gains 6."),
    ("e5", ["(11)^x+3", "(11)^y+2", "1^5", "(11)^z"], 2, "`5` becomes `3`, the last block gains 6."),
    ("e3", ["(11)^x+3", "(11)^y+2", "1^3", "(11)^z"], 2, "`3` becomes `1`, the last block gains 6."),
    ("e1", ["(11)^x+3", "(11)^y+3", "1", "(11)^z"], 2,
     "The block `1` disappears: the first block loses 2, the second 3, the last gains 9."),
    ("loop_e", ["(11)^x+3", "1 (11)^y+2", "(11)^z"], 2,
     "The main round, three blocks with an odd middle one: first and middle lose 2, the last (even) gains 6."),
    ("loop_o", ["(11)^x+3", "1 (11)^y+2", "1 (11)^z"], 2,
     "The main round with an odd last block."),
    ("loop4_e", ["1^4", "1 (11)^y+2", "(11)^z"], 2, "`loop_e` with a first block of 4."),
    ("loop4_o", ["1^4", "1 (11)^y+2", "1 (11)^z"], 2, "`loop_o` with a first block of 4."),
    ("loop3_e", ["(11)^x+3", "1^3", "(11)^z"], 2, "`loop_e` with a middle block of 3."),
    ("loop3_o", ["(11)^x+3", "1^3", "1 (11)^z"], 2, "`loop_o` with a middle block of 3."),
    ("loop43_e", ["1^4", "1^3", "(11)^z"], 2, "`loop_e` with blocks 4 and 3."),
    ("loop43_o", ["1^4", "1^3", "1 (11)^z"], 2, "`loop_o` with blocks 4 and 3."),
    ("o0", ["(11)^x+3", "1 (11)^y+2"], 2, "Two blocks, the right one odd: both lose 2 and a block `6` is appended."),
    ("o0_four", ["1^4", "1 (11)^y+2"], 2, "The same with a first block of 4."),
    ("end1_e", ["(11)^x+4", "1", "(11)^z"], 4, "The middle block is down to `1`: it merges into the last one."),
    ("end1_o", ["(11)^x+4", "1", "1 (11)^z"], 4, "The same with an odd last block."),
    ("end1_six_e", ["1^6", "1", "(11)^z"], 4, "`end1_e` with a first block of 6."),
    ("end1_six_o", ["1^6", "1", "1 (11)^z"], 4, "`end1_o` with a first block of 6."),
    ("end2_e", ["1 1", "1 (11)^y+2", "(11)^z"], 3, "The first block is down to 2: the middle block becomes the first."),
    ("end2_o", ["1 1", "1 (11)^y+2", "1 (11)^z"], 3, "The same with an odd last block."),
    ("end2_three_e", ["1 1", "1^3", "(11)^z"], 3, "`end2_e` with a middle block of 3."),
    ("end2_three_o", ["1 1", "1^3", "1 (11)^z"], 3, "`end2_o` with a middle block of 3."),
    # Short second blocks (an even right block below 18) and a first block of 4: these complete `mapc` so that it
    # needs no `.small` case (the orbit from (74, 30) then stays in the domain by `orbit_dom`).
    ("e0_three", ["(11)^x+3", "(11)^3"], 2, "A right block of 6: a block `9` is split off, leaving `2`."),
    ("e9_one", ["(11)^x+3", "1 1", "1^9"], 4, "Blocks `2, 9` after the first: they merge into `12` and the first gains 6."),
    ("e7_one", ["(11)^x+3", "1 1", "1^7", "(11)^z"], 4, "Blocks `2, 7, z`: the first gains 4, the last 12, `2` and `7` vanish."),
    ("e5_one", ["(11)^x+3", "1 1", "1^5", "(11)^z"], 4, "Blocks `2, 5, z`: the first gains 2, the last 12."),
    ("e3_one", ["(11)^x+3", "1 1", "1^3", "(11)^z"], 4, "Blocks `2, 3, z`: the first is unchanged, the last gains 12."),
    ("e1_one", ["(11)^x+4", "1 1", "1", "(11)^z"], 4, "Blocks `2, 1, z`: the first loses 2, the last gains 12."),
    ("e1_one_six", ["1^6", "1 1", "1", "(11)^z"], 4, "`e1_one` with a first block of 6."),
    ("e1_two", ["(11)^x+3", "1^4", "1", "(11)^z"], 2, "Blocks `4, 1, z`: the first loses 2, `4` becomes `1`, the last gains 9."),
    ("e0_four", ["1^4", "(11)^y+4"], 2, "`e0` with a first block of 4."),
    ("e9_four", ["1^4", "(11)^y+2", "1^9"], 2, "`e9` with a first block of 4."),
    ("e7_four", ["1^4", "(11)^y+2", "1^7", "(11)^z"], 2, "`e7` with a first block of 4."),
    ("e5_four", ["1^4", "(11)^y+2", "1^5", "(11)^z"], 2, "`e5` with a first block of 4."),
    ("e3_four", ["1^4", "(11)^y+2", "1^3", "(11)^z"], 2, "`e3` with a first block of 4."),
    ("e1_four", ["1^4", "(11)^y+3", "1", "(11)^z"], 2, "`e1` with a first block of 4: it becomes 2."),
    ("e0_three_four", ["1^4", "(11)^3"], 2, "`e0_three` with a first block of 4."),
    ("e9_one_four", ["1^4", "1 1", "1^9"], 4, "`e9_one` with a first block of 4."),
    ("e7_one_four", ["1^4", "1 1", "1^7", "(11)^z"], 4, "`e7_one` with a first block of 4."),
    ("e5_one_four", ["1^4", "1 1", "1^5", "(11)^z"], 4, "`e5_one` with a first block of 4."),
    ("e3_one_four", ["1^4", "1 1", "1^3", "(11)^z"], 4, "`e3_one` with a first block of 4."),
    ("e1_two_four", ["1^4", "1^4", "1", "(11)^z"], 2, "`e1_two` with a first block of 4."),
]

# halting rounds: (name, start blocks, doc)
HALTS = [
    ("halt4_e", ["1^4", "1", "(11)^z"], "Middle block 1 with a first block of 4: the machine halts."),
    ("halt4_o", ["1^4", "1", "1 (11)^z"], "The same with an odd last block."),
    ("halt2_e", ["1 1", "1", "(11)^z"], "Middle block 1 with a first block of 2: the machine halts."),
    ("halt2_o", ["1 1", "1", "1 (11)^z"], "The same with an odd last block."),
    ("halt4_one", ["1^4", "1 1", "1", "(11)^z"], "Blocks `4, 2, 1, z`: the machine halts."),
]


def halt_end(start):
    """The configuration just before the halting transition."""
    from bbtools.symtm import Halted, step
    m = Machine.parse(M)
    cfg = Config.parse(start)
    for _ in range(200000):
        c2 = cfg.copy()
        try:
            run(m, c2, lambda c: True, max_moves=1)
            step(m, c2)
        except Halted:
            return cfg
        # advance one move (shift rule or step) on cfg
        trace = []
        n = [0]
        run(m, cfg, lambda c: (n.__setitem__(0, n[0] + 1) or n[0] > 1), max_moves=2, rotate=True)
    raise RuntimeError("no halt")


def main():
    ths = []
    for name, bl, count, doc in RULES:
        start = K(*bl)
        end = run_to(start, count)
        th, _ = prove(M, name, start, end, doc=doc, rotate=True, count_first=True, max_seg=40)
        ths.append(th)
    for name, bl, doc in HALTS:
        start = K(*bl)
        end = halt_end(start)
        th, _ = prove(M, name, start, end, doc=doc, rotate=True, count_first=True, max_seg=40)
        ths.append(th)
    sys.stdout.write(rules_file("Machine", "H35366", ths, f"Rounds of {M}, generated by `py/rules.py`; do not edit by hand."))


if __name__ == "__main__":
    main()
