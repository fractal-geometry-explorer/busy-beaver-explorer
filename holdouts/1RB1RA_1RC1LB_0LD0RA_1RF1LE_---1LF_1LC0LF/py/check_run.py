"""Read the run from blank tape at the moments the head is in C at the right end of the visited cells
(`tmrun MACHINE STEPS at C R K` output on stdin) and classify each move between consecutive block configurations:
an odd round, an even round (the laws of verify_rounds.py, with their exact step counts), or another
move (printed).

usage: tmrun 1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF 30000000000 at C R 100000 | python3 check_run.py
"""
import re, sys


def parse(tape):
    cells = []
    for tok in tape.split():
        m = re.fullmatch(r"([A-F])>([01])", tok)
        if m:
            if m.group(1) != "C" or m.group(2) != "0":
                return None
            continue
        c, _, k = tok.partition("^")
        cells += [int(c)] * (int(k) if k else 1)
    s = "".join(map(str, cells)).strip("0")
    if "00" in s or not s or not cells or cells[-1] != 1:
        return None
    return [len(x) for x in s.split("0")]


def main():
    prev = None
    counts = {"odd": 0, "even": 0, "other": 0}
    for line in sys.stdin:
        f = line.split(None, 1)
        if len(f) < 2 or not f[0].isdigit():
            continue
        t, bl = int(f[0]), parse(f[1])
        if bl is None:
            continue
        if prev:
            (t0, b0) = prev
            *pre, A, n = b0 if len(b0) >= 2 else [None] + b0
            if A is not None and n % 2 == 1 and 3 <= n <= 2 * A + 1 and bl == b0[:-1] + [n + 2] \
                    and t - t0 == 3 * 2 ** ((n + 3) // 2) - 6:
                counts["odd"] += 1
            elif A is not None and n % 2 == 0 and 4 <= n <= 2 * A + 2 and bl == b0[:-2] + [A - 1, n - 1, 3] \
                    and t - t0 == 6 * 2 ** (n // 2) - 2 * n - 2:
                counts["even"] += 1
            else:
                counts["other"] += 1
                print(f"other: step {t0:>14,} {b0} -> step {t:>14,} {bl}  ({t - t0:,} steps)")
        prev = (t, bl)
    print("last:", prev)
    print(counts)


if __name__ == "__main__":
    main()
