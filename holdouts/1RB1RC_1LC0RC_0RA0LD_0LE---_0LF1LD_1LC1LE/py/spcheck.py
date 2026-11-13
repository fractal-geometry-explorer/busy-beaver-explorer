"""Check the motion of the separators between bounces, from the output of c/seppos.c.

At each bounce (the head at the left end, turning right) seppos prints the positions of all cells that are not
inside a run of 10s: the left-end 0, the single-0 separators and the two cells of each wall.  Between two bounces
with the same number of separators before the first wall (no collision in between), the k-th separator before the
wall should move 2 cells to the right for odd k and stay for even k, and the first wall should move 0 or 2 cells.

usage: gcc -O2 -I tools/c -o seppos c/seppos.c && ./seppos MACHINE 300000000 0 > sp.txt && python3 py/spcheck.py sp.txt
"""
import sys


def main(path):
    prev, ok, bad, wall_ok, wall_bad = None, 0, 0, 0, 0
    for line in open(path):
        a, b = line.split(":")
        k, lo, hi = map(int, a.split())
        pos = [int(x[:-1]) for x in b.split()][1:]
        w = next((i for i in range(len(pos) - 1) if pos[i + 1] == pos[i] + 1), None)
        act = pos[:w] if w is not None else pos
        cur = (act, pos[w] if w is not None else None)
        if prev and len(prev[0]) == len(act) and prev[1] is not None and cur[1] is not None:
            d = [y - x for x, y in zip(prev[0], act)]
            if d == [2 if i % 2 == 0 else 0 for i in range(len(d))]:
                ok += 1
            else:
                bad += 1
            if cur[1] - prev[1] in (0, 2):
                wall_ok += 1
            else:
                wall_bad += 1
        prev = cur
    print(f"separators: {ok} bounces as predicted, {bad} not; first wall: {wall_ok} as predicted, {wall_bad} not")


if __name__ == "__main__":
    main(sys.argv[1])
