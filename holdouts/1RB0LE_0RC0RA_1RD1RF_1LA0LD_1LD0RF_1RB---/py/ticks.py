"""Every tick of 1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB--- (one round trip from the right end back to it), as a
symbolic rule on the block list.

usage: ./blocks STEPS | python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/ticks.py
       (c/blocks.c prints the block list `n0 s1 n1 ... nk` at every right-end turn, s = '|' or '.')

For each block list, the last few blocks are written with their lengths as variables (`(1010)^v` padded so that the
parity is fixed; blocks of length <= 3 stay literal), the rest of the tape is an unknown context, and the machine
is run symbolically (`bbtools.symtm`, shift rules over the runs) until it is back at the right end in the same
situation `A> 1 1`.  The shortest suffix for which the run never looks into the unknown context gives the rule of
that tick.  Ticks are grouped by the pattern of the suffix: separators, and for each block `e` (even, >= 4), `o`
(odd, >= 5) or its literal length `cN`.  Printed per pattern: how many ticks, and the rule in block notation (the
first number is the end of the block before the suffix).  Ticks whose rule needs the left end of the tape are
counted as `left end` (the rebuilds); they are not described here.

This is a symbolic computation, not a Lean proof; two of the patterns are proved in Lean (`tick_last`, `tick_oo`).
"""
import os
import re
import sys
from collections import OrderedDict, Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.symtm import Config, run, TouchContext, NeedSplit, Rep, Lin, Blank, Ctx  # noqa: E402
from bbtools.machine import Machine  # noqa: E402

M = Machine.parse("1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---")
SMALL = 3


def block(n, v):
    if n <= SMALL:
        return " ".join("10" * n), "c%d" % n
    if n % 2 == 0:
        return f"1 0 (1010)^{v} 1 0", "e"
    return f"1 0 (1010)^{v} 1 0 1 0", "o"


def template(nums, seps, i):
    parts, key = ["L", "1" if seps[i - 1] == "|" else "0"], [seps[i - 1]]
    for j in range(i, len(nums)):
        s, k = block(nums[j], f"v{j}")
        if s:
            parts.append(s)
        key.append(k)
        if j < len(nums) - 1:
            parts.append("1" if seps[j] == "|" else "0")
            key.append(seps[j])
    parts.append("A> 1 1 0^inf")
    return " ".join(parts), "".join(key)


def at_end(c):
    r = c.right
    return (c.state == 0 and len(r) == 3 and r[0] == 1 and r[1] == 1 and isinstance(r[2], Blank)
            and not c.steps.is_zero())


def tick(nums, seps):
    for i in range(len(nums) - 1, 0, -1):
        s, key = template(nums, seps, i)
        c = Config.parse(s)
        try:
            run(M, c, at_end, max_moves=5000, rotate=True)
            return key, s, c
        except TouchContext:
            continue
        except NeedSplit:
            return key, s, None
    return None


def half(x):
    if x.k % 2 == 0 and all(v % 2 == 0 for v in x.c.values()):
        return repr(Lin(x.k // 2, {k: v // 2 for k, v in x.c.items()})).replace(" ", "")
    return "(" + repr(x) + ")/2"


def blocks_of(cfg):
    """The block notation of the tape left of the head (after `1 0`, the end of the block before the suffix)."""
    segs = [(1, 1, Lin(1)), (0, 0, Lin(1))]
    for t in cfg.left:
        if isinstance(t, Rep):
            segs.append((t.word[0], t.word[-1], len(t.word) * t.n))
        elif isinstance(t, int):
            segs.append((t, t, Lin(1)))
    out, cur, prev = [], Lin(0), None
    for f, last, n in segs:
        if prev is not None and prev == f:
            if f == 1:           # a pair 11: the separator is the first 1
                out += [cur - 1, "|"]
                cur = Lin(0)
            else:                # a pair 00: the separator is the second 0
                out += [cur, "."]
                cur = Lin(-1)
        cur, prev = cur + n, last
    out.append(cur)
    return " ".join(x if isinstance(x, str) else half(x) for x in out)


def main():
    rules, other = OrderedDict(), Counter()
    for line in sys.stdin:
        parts = line.split()
        if len(parts) < 2 or parts[0] == "HALT":
            continue
        nums = list(map(int, re.findall(r"\d+", parts[1])))
        seps = re.findall(r"[|.]", parts[1])
        if len(nums) < 2:
            other["left end"] += 1
            continue
        r = tick(nums, seps)
        if r is None:
            other["left end"] += 1
            continue
        key, s, c = r
        if c is None:
            other["needs a finer split: " + key] += 1
            continue
        if key not in rules:
            rules[key] = [0, blocks_of(Config.parse(s)), blocks_of(c), c.steps]
        rules[key][0] += 1
    for key, (n, a, b, st) in sorted(rules.items(), key=lambda kv: -kv[1][0]):
        print(f"{n:7d}  {key:22s} {a}  ==>  {b}   [{st} steps]")
    print(f"{len(rules)} patterns; " + ", ".join(f"{k}: {v}" for k, v in other.items()))


if __name__ == "__main__":
    main()
