"""Check the base-4 countdown of 1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RD against a run.

usage:  gcc -O2 -o turns c/turns.c
        ./turns 1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RD 300000000 100000000 30 | python3 py/check_countdown.py

Reads the tape at every turn of the head (raw cells, `>` before the head) and keeps the turns in state A just
right of the growing block w^n (w = 111110).  The tape right of the head is parsed into blocks v^x (v = 101110)
separated by r = 10, q = 1110, p = 101011, s = 11, as far as they go.  A tick moves the left end of the tape by 12
cells; the turns half way through a tick (6 cells) are told apart by the length of the tape mod 12, the class in
which the rule holds being found from the data.  The rule, for a borrow arriving at a separator between blocks
x (left) and z (right):  r -> q, z - 1;  q -> p, x - 1;  p -> s;  s -> r, x - 1, z + 1 and the borrow goes on to
the next separator.  Each tick sends a borrow into the separator after the first block (the timer).
"""
import sys

SEPS = (("101011", 1), ("1110", 2), ("10", 3), ("11", 0))
V = "101110"


def parse(r):
    blocks, ds = [], []
    while True:
        n = 0
        while r.startswith(V):
            r, n = r[6:], n + 1
        blocks.append(n)
        for w, d in SEPS:
            if r.startswith(w) and r[len(w):].startswith(V):
                ds.append(d)
                r = r[len(w):]
                break
        else:
            return blocks, ds, r


def tick(blocks, ds):
    b, d, j = list(blocks), list(ds), 0
    while j < len(d):
        if d[j] == 3:
            b[j + 1] -= 1
            d[j] = 2
        elif d[j] == 2:
            b[j] -= 1
            d[j] = 1
        elif d[j] == 1:
            d[j] = 0
        else:
            b[j] -= 1
            b[j + 1] += 1
            d[j] = 3
            j += 1
            continue
        return b, d
    return None


def main():
    rows = []
    for line in sys.stdin:
        f = line.split()
        if len(f) < 4 or f[2] != "A":
            continue
        left, right = f[3].split(">")
        if not left.endswith("1111101"):
            continue
        rows.append((len(left),) + parse(right))
    best = None
    for cls in range(12):
        ok = bad = other = 0
        for i, (n, b, d, rest) in enumerate(rows):
            if n % 12 != cls:
                continue
            nxt = [r for r in rows[i + 1:i + 6] if r[0] == n + 12]
            if not nxt:
                other += 1
                continue
            n2, b2, d2, rest2 = nxt[0]
            p = tick(b, d)
            if p is None or rest2 != rest or len(b2) != len(b):
                other += 1
            elif p == (b2, d2):
                ok += 1
            else:
                bad += 1
        if best is None or ok > best[1]:
            best = (cls, ok, bad, other)
    cls, ok, bad, other = best
    print(f"tick starts (tape length = {cls} mod 12): {ok} follow the rule exactly, {bad} do not, "
          f"{other} change the structure (a block runs out or the borrow runs past the parsed blocks)")


if __name__ == "__main__":
    main()
