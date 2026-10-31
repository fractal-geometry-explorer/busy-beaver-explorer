"""The pass structure of 1RB1RA_1LC1LD_1LD0LB_1RE0RF_---1RD_1RA1RB from blank tape.

The run keeps returning to A on the blank cell right of the tape, `1^{b_1} 0 1^{b_2} 0 ... 0 1^{b_k} A> 0^inf` (blocks
of ones separated by single 0s).  `next_pass` is one pass on the block list, as `lean/Macro.lean` (`next`,
`next_sound`) proves it, when the last block is not a multiple of 3; that case is recursive (the converter carries on
into the next block) and `next_pass` gives None for it.

usage:
  python3 py/macro.py passes STEPS [K]     the pass starts of the run from blank tape (block lists), at most K lines
  python3 py/macro.py check STEPS          compare next_pass with the run: every non-recursive pass, and a census
  python3 py/macro.py check-file FILE      the same for `tools/c/tmrun MACHINE STEPS at A R N` output (grep 'A>0$')
"""
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools", "py"))

from bbtools.machine import Machine, Run  # noqa: E402

M = "1RB1RA_1LC1LD_1LD0LB_1RE0RF_---1RD_1RA1RB"
MACHINE = Machine.parse(M)
A = 0
HALT = "halt"


def next_pass(blocks):
    """The next pass start, as a tuple of blocks (left to right); HALT if the machine halts on this pass (last block
    1); None if the last block is a multiple of 3 (not covered).  Missing blocks at the left end count as 0.  The
    same function as `next` in lean/Macro.lean, written with b = n + 1 the last block."""
    *rest, b = blocks
    x = rest[-1] if rest else 0
    d = rest[-2] if len(rest) >= 2 else 0
    if b == 1:
        return HALT
    if b % 3 == 0:
        return None
    if b % 3 == 1:                      # n = b - 1 = 3m: the block to the left gains 6 + 2*floor((m - 1)/2)
        m = (b - 1) // 3
        return tuple(rest[:-1]) + (x + 6 + 2 * ((m - 1) // 2), 2 * m - 1)
    m = (b - 2) // 3                    # b = 3m + 2: two blocks to the left are rebuilt
    return tuple(rest[:-2]) + (d + 2 + 2 * ((m + 1) // 2), x + 2 * m + 3)


def blocks_of(cells):
    s = "".join(map(str, cells)).strip("0")
    return tuple(len(p) for p in s.split("0"))


def pass_starts(steps):
    """Yield (step, blocks) each time A reads the blank cell right of the visited tape, from blank tape: the macro
    configuration.  Raises if a separator is not a single 0 (it never is in the runs checked)."""
    r = Run(MACHINE)
    while r.steps < steps and r.step():
        if r.state == A and r.head == r.tape.hi and r.tape.get(r.head) == 0:
            w = r.tape.word(r.tape.lo, r.head - 1)
            bl = blocks_of(w)
            if 0 in bl:
                raise ValueError(f"step {r.steps}: a separator of more than one 0: {r.config_str()}")
            yield r.steps, bl


def parse_tmrun(line):
    """(step, blocks) from a line `STEPS 1^a 0 1^b ... A>0` of tools/c/tmrun."""
    parts = line.split()
    bl = []
    for tok in parts[1:-1]:
        if tok.startswith("1"):
            bl.append(int(tok[2:]) if "^" in tok else 1)
        elif tok != "0":
            raise ValueError(f"a separator of more than one 0: {line.strip()}")
    return int(parts[0]), tuple(bl)


def check(seq):
    """Compare next_pass with consecutive pass starts. Returns (agree, recursive, census of last block mod 3,
    largest number of blocks)."""
    agree, rec, mod3, most = 0, 0, Counter(), 0
    prev = None
    for _, bl in seq:
        most = max(most, len(bl))
        if prev is not None:
            mod3[prev[-1] % 3] += 1
            p = next_pass(prev)
            if p is None:
                rec += 1
            elif p != bl:
                raise AssertionError(f"next_pass{prev} = {p}, the run gives {bl}")
            else:
                agree += 1
        prev = bl
    return agree, rec, mod3, most


def main(argv):
    if not argv:
        print(__doc__)
        return
    cmd = argv[0]
    if cmd == "passes":
        k = int(argv[2]) if len(argv) > 2 else 200
        for n, (t, bl) in enumerate(pass_starts(int(argv[1]))):
            if n >= k:
                break
            print(t, " ".join(map(str, bl)))
    elif cmd in ("check", "check-file"):
        seq = pass_starts(int(argv[1])) if cmd == "check" else (parse_tmrun(l) for l in open(argv[1]) if l.strip())
        agree, rec, mod3, most = check(seq)
        print(f"passes: {agree + rec}; next_pass agrees with the run on all {agree} it covers; {rec} recursive "
              f"(last block 0 mod 3); last block mod 3: {dict(sorted(mod3.items()))}; at most {most} blocks")
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
