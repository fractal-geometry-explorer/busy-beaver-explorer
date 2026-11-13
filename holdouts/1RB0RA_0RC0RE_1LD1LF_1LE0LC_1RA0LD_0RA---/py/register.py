"""The register of 1RB0RA_0RC0RE_1LD1LF_1LE0LC_1RA0LD_0RA---.

Each time the head is in A at the right end, cut the tape into three-cell digits from the right (after the final
1): the tail is the run of 110 at the end; before it the register is the longest stretch of digits 110 (1) and
010 (0) (the tail's own 110s excluded). Prints the step, the tail length, the register length and the register's
low (right) end, and at the end how far from the low end each sweep changed the register.

usage: python3 register.py [STEPS] [EVERY]     (default 3e6 steps, print every 20th sample)
"""
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.machine import Machine, Run  # noqa: E402

M = "1RB0RA_0RC0RE_1LD1LF_1LE0LC_1RA0LD_0RA---"


def split(cells):
    """(tail, register) of a tape that ends in 1 at the head's left."""
    s = "".join(map(str, cells))
    if not s.endswith("1"):
        return 0, ""
    s = s[:-1]
    blocks = [s[i - 3:i] for i in range(len(s), 2, -3)]
    t = 0
    while t < len(blocks) and blocks[t] == "110":
        t += 1
    reg = []
    for b in blocks[t:]:
        if b == "110":
            reg.append("1")
        elif b == "010":
            reg.append("0")
        else:
            break
    # the tail's last block may belong to the register's low end; keep the convention of the README: tail = run of 110
    return t, "".join(reversed(reg))


def main():
    steps = float(sys.argv[1]) if len(sys.argv) > 1 else 3e6
    every = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    r = Run(Machine.parse(M))
    n = 0
    prev = None
    depth = Counter()
    while r.steps < steps:
        if not r.step():
            print("halted after", r.steps, "steps")
            return
        if r.state == 0 and r.head == r.tape.hi and r.tape.get(r.head) == 0 and r.steps > 100:
            t, reg = split(r.tape.word(r.tape.lo, r.head - 1))
            if prev is not None and len(prev) == len(reg) and prev != reg:
                i = next(j for j in range(len(reg)) if reg[j] != prev[j])
                depth[(len(reg) - i) // 20 * 20] += 1
            prev = reg if reg else prev
            if n % every == 0:
                print(f"{r.steps:>10}  tail {t:5d}  register {len(reg):3d}  ...{reg[-50:]}")
            n += 1
    print("leftmost changed digit, counted from the low end, per sweep (bins of 20):", sorted(depth.items()))


if __name__ == "__main__":
    main()
