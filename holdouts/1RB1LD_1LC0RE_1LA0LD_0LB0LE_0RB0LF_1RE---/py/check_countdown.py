"""Check the base-3 countdown of 1RB1LD_1LC0RE_1LA0LD_0LB0LE_0RB0LF_1RE--- against a run.

usage:  gcc -O2 -o turns c/turns.c
        ./turns 1RB1LD_1LC0RE_1LA0LD_0LB0LE_0RB0LF_1RE--- 200000000 100000000 30 | python3 py/check_countdown.py

Reads the tape at every turn of the head (raw cells, `>` before the head) and keeps the E-turns at the right end,
`... (1000)^x 10100 E> 0 (1110)^y 111111`.  Each is parsed from the right into blocks (1000)^x separated by the
standard separators c = 101010, 10, 00, as far as they go.  For consecutive ticks it checks the rule: with
N = 3x + e (e = 2, 0, 1 for c, 10, 00 on the block's left), a borrow lowers N by 2 and moves one block left exactly
when N mod 3 goes from 1 to 2; each tick sends one borrow into the timer and adds 4 to y.
"""
import re
import sys

TICK = re.compile(r"10100>0(1110)+111111$")
SEPS = (("101010", 2), ("10", 0), ("00", 1))


def parse(tape):
    left, right = tape.split(">")
    left = left[:-5]
    y = (len(right) - 7) // 4
    blocks, es = [], []
    while True:
        n = 0
        while left.endswith("1000"):
            left, n = left[:-4], n + 1
        blocks.append(n)
        for w, e in SEPS:
            if left.endswith(w) and left[:-len(w)].endswith("1000"):
                es.append(e)
                left = left[:-len(w)]
                break
        else:
            break
    blocks.reverse()
    es.reverse()
    # N for every block that has a standard separator on its left
    return left, [3 * blocks[i] + es[i - 1] for i in range(1, len(blocks))], y


def predict(ns):
    """The N list after one tick, and whether the borrow ran past the parsed blocks."""
    p, i = list(ns), len(ns) - 1
    while True:
        p[i] -= 2
        if p[i] % 3 == 2:
            if i == 0:
                return p, True
            i -= 1
            continue
        return p, False


def main():
    prev = None
    exact = past = other = bad = 0
    for line in sys.stdin:
        f = line.split()
        if len(f) < 4 or not TICK.search(f[3]):
            continue
        cur = parse(f[3])
        if prev and prev[1] and cur[2] == prev[2] + 4:
            p, ran = predict(prev[1])
            if cur[0] == prev[0] and len(cur[1]) == len(prev[1]):
                if p == cur[1] and not ran:
                    exact += 1
                else:
                    bad += 1
                    print("MISMATCH at step", f[0])
            elif ran:
                past += 1
            else:
                other += 1
        prev = cur
    print(f"{exact} ticks follow the rule exactly, {bad} do not; {past} borrows run past the standard blocks "
          f"(as predicted); {other} other changes (blocks running out)")


if __name__ == "__main__":
    main()
