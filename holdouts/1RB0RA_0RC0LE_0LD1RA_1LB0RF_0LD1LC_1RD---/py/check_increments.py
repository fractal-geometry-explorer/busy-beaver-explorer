"""Checks the counter increment rule against a direct simulation (python3 check_increments.py [STEPS]).

Each time the head reaches a new cell on the right in state C with the tape ending in `... 0 0 (10)^m`, the tape
is read from the right as: reservoir (10)^m, the marker 0 0, then pairs (digit, block) = (0 or 1, (10)^n) as far
as the tape keeps that form. Between two such moments with the reservoir down by 2, the rule predicts: the low
1-digits become 0, the next 0 becomes 1, its block and the lowest block each gain two 10s, the rest is unchanged.
The rule is checked when all blocks up to one past the carry have even length; counts the increments that match,
those that do not (none expected), the carries that reach an odd block (higher-level separators, outside the
rule) and the reservoir refills (m not down by 2, where the rule does not apply)."""
import re, sys

M = "1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---"


def table(m):
    t = {}
    for i, part in enumerate(m.split("_")):
        for r in (0, 1):
            x = part[3 * r:3 * r + 3]
            if x[2] != "-":
                t[(i, r)] = (int(x[0]), 1 if x[1] == "R" else -1, ord(x[2]) - 65)
    return t


def digits(cells):
    """Read the tape (list of 0/1 up to the head) from the right; None unless it ends in 0 0 (10)^m."""
    i = len(cells)

    def pairs(i):
        n = 0
        while i >= 2 and cells[i - 2] == 1 and cells[i - 1] == 0:
            i -= 2
            n += 1
        return i, n

    i, m = pairs(i)
    if m == 0 or i < 2 or cells[i - 1] != 0 or cells[i - 2] != 0:
        return None
    i -= 2
    ds = []
    while True:
        j, n = pairs(i)
        if n == 0 or j < 3:
            break
        ds.append([cells[j - 1], n])
        i = j - 1
        if not (cells[i - 1] == 0 and cells[i - 2] == 1):
            ds.pop()
            break
    return i, ds, m


def main(steps):
    t = table(M)
    tape, pos, st, right = [0] * 64, 0, 0, 0
    ok = bad = refill = deep = 0
    prev = None
    for n in range(steps):
        r = tape[pos]
        if (st, r) not in t:
            print("halt at step", n)
            return
        w, d, st = t[(st, r)]
        tape[pos] = w
        pos += d
        if pos >= len(tape):
            tape.extend([0] * len(tape))
        if pos > right:
            right = pos
            if st == 2:
                cur = digits(tape[:pos])
                if cur:
                    if prev and cur[2] == prev[2] - 2:
                        ds = [x[:] for x in prev[1]]
                        j = 0
                        while j < len(ds) and ds[j][0] == 1:
                            ds[j][0] = 0
                            j += 1
                        if j + 1 < len(ds) and all(x[1] % 2 == 0 for x in ds[:j + 2]):
                            ds[j][0] = 1
                            ds[j][1] += 2
                            ds[0][1] += 2
                            k = min(len(ds), len(cur[1]))
                            if ds[:k] == cur[1][:k]:
                                ok += 1
                            else:
                                bad += 1
                                print("mismatch at step", n, prev[1][:8], cur[1][:8])
                        else:
                            deep += 1
                    elif prev:
                        refill += 1
                    prev = cur
    print(f"{steps} steps: {ok} increments match the rule, {bad} do not; "
          f"{deep} carries reach a block of odd length (outside the rule), {refill} reservoir refills")


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 3_000_000)
