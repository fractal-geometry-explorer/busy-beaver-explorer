"""Resets of 1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC---: reads the output of `sim MACHINE STEPS 1` on stdin and prints,
at each visit of the left end in state B where the leading (110)^k has shrunk, the rest of the tape as the list of
(10)-group lengths, run-length coded (4^1295 = 1295 groups (10)^4 in a row).

usage: ./sim 1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC--- 600000000 1 | python3 resets.py
"""
import re
import sys

pk = -1
for line in sys.stdin:
    p = line.split(" ", 2)
    if len(p) < 3 or p[1] != "LB":
        continue
    t = p[2].strip()[5:]
    m = re.match(r"((?:110)*)(.*)", t)
    k, rest = len(m.group(1)) // 3, m.group(2)
    if k < pk:
        rl = []
        for b in (len(x) // 2 for x in re.findall(r"(?:10)+", rest)):
            if rl and rl[-1][0] == b:
                rl[-1][1] += 1
            else:
                rl.append([b, 1])
        print(p[0], "k", pk, "->", k, " ".join(f"{b}^{c}" if c > 1 else str(b) for b, c in rl)[:200], flush=True)
    pk = k
