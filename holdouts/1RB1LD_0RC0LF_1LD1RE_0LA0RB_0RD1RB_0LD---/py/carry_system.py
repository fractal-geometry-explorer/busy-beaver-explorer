"""Replay 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD--- with the rules of the carry system and compare with the machine.

The rules (lean/Carry.lean proves each one; `>` is B about to read the next cell, `<` is D on the cell before it):

  R1 >011 -> 011>   R2 >0100 -> 011>0   R3 >0101 -> 0100>   R4 >00 -> 0<1   R5 0>1 -> <00
  L1 10< -> <10     L2 00< -> 1>0       L3 1< -> 0>         halt: >0111

The run from blank tape starts with one step of state A, `1>`.  This script applies rules N times, adds up the
machine steps each rule stands for, and every CHECK rule applications runs the plain machine to the same step
count and compares tape, head and state.  It prints how often each rule was used.

usage: python3 carry_system.py [N=2000000] [CHECK=50000]"""
import os
import sys
from collections import Counter, defaultdict
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.machine import Machine

M = "1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---"


class Carry:
    """tape: dict cell -> 0/1; mode '>' (B on cell p) or '<' (D on cell p)."""

    def __init__(self):
        self.t = defaultdict(int)
        self.t[0] = 1
        self.p, self.mode, self.steps, self.halted = 1, '>', 1, False
        self.used = Counter()

    def rule(self):
        t, p = self.t, self.p
        if self.mode == '>':
            if t[p] == 1:
                if t[p - 1] == 1:                      # only reached as >0111 (see halt_pattern)
                    self.halted = True; self.steps += 2; return 'halt'
                t[p] = 0; self.p = p - 2; self.mode = '<'; self.steps += 2; return 'R5'
            if t[p + 1] == 0:
                t[p + 1] = 1; self.mode = '<'; self.steps += 2; return 'R4'
            if t[p + 2] == 1:
                self.p = p + 3; self.steps += 3; return 'R1'
            if t[p + 3] == 0:
                t[p + 2] = 1; self.p = p + 3; self.steps += 5; return 'R2'
            t[p + 3] = 0; self.p = p + 4; self.steps += 4; return 'R3'
        if t[p] == 1:
            t[p] = 0; self.p = p + 1; self.mode = '>'; self.steps += 1; return 'L3'
        if t[p - 1] == 1:
            self.p = p - 2; self.steps += 2; return 'L1'
        t[p - 1] = 1; self.mode = '>'; self.steps += 2; return 'L2'


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 2000000
    chk = int(sys.argv[2]) if len(sys.argv) > 2 else 50000
    m = Machine.parse(M)
    c = Carry()
    tape, pos, st, done = defaultdict(int), 0, 0, 0
    for i in range(1, n + 1):
        r = c.rule()
        c.used[r] += 1
        if r == 'halt':
            print("halt after", c.steps, "steps"); break
        if i % chk == 0 or i == n:
            while done < c.steps:
                w, d, s2 = m.table[st][tape[pos]]
                tape[pos] = w; pos += d; st = s2; done += 1
            ok = (pos == c.p and "ABCDEF"[st] == ('B' if c.mode == '>' else 'D')
                  and all(tape[k] == c.t[k] for k in set(tape) | set(c.t)))
            if not ok:
                print("MISMATCH at rule", i, "step", c.steps); sys.exit(1)
    print(f"{n} rule applications = {c.steps} machine steps, all checks agree")
    print("rules used:", dict(sorted(c.used.items())))


if __name__ == "__main__":
    main()
