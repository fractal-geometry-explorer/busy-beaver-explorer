"""The sample map of 1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---, measured by direct simulation.

Sample: the head in B on the left end of the tape, K(pre, N, S) = 0^inf B> 0 0 pre 1^N S 0^inf with pre '' or '10'
and S a short word on the right.  `run(pre, N, S)` runs to the next sample with a block of at least max(8, N/3)
ones.  The map is measured, not proved.

usage: python3 kmap.py        prints the map for N = 20..31 and a few (pre, S)
"""
import re

TABLE = "1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---"


def parse(m):
    t = []
    for g in m.split("_"):
        row = []
        for y in (0, 1):
            s = g[3 * y:3 * y + 3]
            row.append(None if s[2] not in "ABCDEF" else (int(s[0]), 1 if s[1] == "R" else -1, "ABCDEF".index(s[2])))
        t.append(row)
    return t


TT = parse(TABLE)


def decode(s):
    m = re.fullmatch(r"0(10)?(1+)(0.*)?", s)
    return None if not m else (m.group(1) or "", len(m.group(2)), m.group(3) or "")


def run(pre, N, S, maxsteps=10 ** 7):
    cells = [0, 0] + [int(c) for c in pre] + [1] * N + [int(c) for c in S]
    tape = {i: c for i, c in enumerate(cells)}
    pos, st, n, lo = 0, 1, 0, 0
    while n < maxsteps:
        tr = TT[st][tape.get(pos, 0)]
        if tr is None:
            return ("HALT", n)
        w, d, st = tr
        tape[pos] = w
        pos += d
        n += 1
        lo = min(lo, pos)
        if st == 1 and pos == lo and tape.get(pos, 0) == 0 and n > 1:
            hi = max(k for k, v in tape.items() if v)
            r = decode("".join(str(tape.get(i, 0)) for i in range(pos + 1, hi + 1)))
            if r and r[1] >= max(8, N // 3):
                return r + (n,)
    return ("TO", n)


def main():
    for pre in ("", "10"):
        for S in ("", "011011"):
            print(f"pre={pre or 'e'} S={S or 'e'}:")
            for N in range(20, 32):
                r = run(pre, N, S)
                print(f"   N={N}: " + (f"pre={r[0] or 'e'} N'={r[1]} S={r[2] or 'e'}" if r[0] not in ("HALT", "TO") else r[0]))


if __name__ == "__main__":
    main()
