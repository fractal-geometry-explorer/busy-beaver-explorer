"""Find the stretches of the run where the left end replays the run from blank tape in front of a long block.

usage: python3 py/replay.py [FILE] [MIN_WALL]

FILE holds the left events "STEPS L WIDTH STATE words" as `tools/c/tokrun MACHINE N a=10,b=110 L K` (or
`py/blank.py left`) prints them; default runs/left_1e10.txt.  Event i of the run from blank tape has the words
`0^2 P a^x 1`: a prefix P, a last block of x pairs, the right end.  When an event j has the words `0^2 a^W 0 ...`
with W >= MIN_WALL (default 50, a "wall" of W pairs), the next events are compared with the run from blank tape:
event j + i replays event i if its words start with `0^2 P a^y` for some y.  Printed: each wall with at least two
replayed events, how many, and the wall's length in the events that replay (it shrinks as the replay grows).

This is an observation about the events (heuristic), not a proof that the replay goes on.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)


def read_events(path):
    out = []
    with open(path) as f:
        for line in f:
            p = line.split()
            if len(p) >= 4 and p[1] == "L":
                out.append((int(p[0]), p[4:]))
    return out


def pairs(w):
    if w == "a":
        return 1
    if w.startswith("a^"):
        return int(w[2:])
    return None


def walls(events, min_wall=50):
    """Yield (step, event index, wall, replayed events, [wall length after each replayed event])."""
    blank = [tk for _, tk in events]
    for j, (t, tk) in enumerate(events):
        if len(tk) < 3 or tk[0] != "0^2" or (pairs(tk[1]) or 0) < min_wall or tk[2] not in ("0", "0^2"):
            continue
        n, rest = 0, []
        for i in range(1, len(events) - j):
            b, r = blank[i], events[j + i][1]
            if len(b) < 3 or b[-1] != "1" or pairs(b[-2]) is None:
                break
            p = b[:-2]
            if r[:len(p)] != p or len(r) <= len(p) + 2 or pairs(r[len(p)]) is None:
                break
            n = i
            rest.append(pairs(r[len(p)]))
        yield t, j, pairs(tk[1]), n, rest


def main(argv):
    path = argv[0] if argv else os.path.join(ROOT, "runs", "left_1e10.txt")
    min_wall = int(argv[1]) if len(argv) > 1 else 50
    for t, j, w, n, rest in walls(read_events(path), min_wall):
        if n >= 2:
            print(f"step {t} (event {j}): wall of {w} pairs; the next {n} events replay events 1..{n} of the run "
                  f"from blank tape")
            print("  the wall after each replayed event:", " ".join(map(str, rest)))


if __name__ == "__main__":
    main(sys.argv[1:])
