"""Windowed abstract run of 1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB with trips into the word as black boxes.

Claim (trip lemma): from `0 0 0 1 1 A> W`, with the head confined right of the five region cells, the machine
never halts, and it either runs forever or steps left of the region in one of six ways EXITS (state, the six
cells from the region start).  Proof by minimal counterexample: in a shortest bad trip every later occurrence of
`0 0 0 1 1 A>` starts a shorter trip, which by minimality is good; so the bad trip is a run of the abstract system
where each such occurrence is replaced by its possible exits, with every cell right of the six made unknown.

The abstract configuration is a window of cells around the head ('0', '1', 'u' unknown, '|' the wall), the rest
unknown.  A cell that leaves the window is forgotten (becomes unknown) - an over-approximation.  The search
reports the reachable halts and exits; the lemma holds if there is no halt and every exit is one of EXITS.

usage: python3 blackbox.py LEFT RIGHT"""
import sys

M = "1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB"
T = {}
for s, g in enumerate(M.split("_")):
    for y in (0, 1):
        x = g[3 * y:3 * y + 3]
        T[(s, y)] = None if x[0] == '-' else (int(x[0]), 1 if x[1] == 'R' else -1, "ABCDEF".index(x[2]))
EXITS = [(1, "111001"), (1, "011011"), (1, "111011"), (4, "111110"), (4, "111101"), (4, "111111")]
LW, RW = int(sys.argv[1]), int(sys.argv[2])
MAXS = int(sys.argv[3]) if len(sys.argv) > 3 else 3_000_000
REGION = "00011"


def norm(st, left, right):
    """left: cells left of the head, nearest last; right: head cell first.  Trim to the window."""
    left = left[-LW:] if len(left) > LW else left
    right = right[:RW + 1]
    right = right.rstrip("u") or ""
    i = 0
    while i < len(left) and left[i] == "u" and "|" not in left:
        i += 1
    return (st, left[i:] if "|" not in left else left, right)


def cell(right):
    return right[0] if right else "u"


start = (0, "|" + REGION, "")
todo, seen, bad, exits = [start], {start}, [], set()
from collections import deque
todo = deque(todo)
first = True
while todo:
    st, left, right = todo.popleft()
    nxt = []
    # black box: `0 0 0 1 1 A>` (not the initial configuration)
    if (st, left, right) != start and st == 0 and left.endswith(REGION):
        pre = left[:-5]
        for s2, cells in EXITS:
            # head on the cell left of the region, in s2; the six cells; everything right of them unknown
            if pre == "" or pre.endswith("|") and len(pre) == 1:
                exits.add((s2, cells))                  # this is an exit of the outer trip itself
                continue
            nxt.append(norm(s2, pre[:-1], pre[-1] + cells))
    else:
        c = cell(right)
        for b in ((0, 1) if c == "u" else (int(c),)):
            tr = T[(st, b)]
            if tr is None:
                bad.append((st, left, right))
                continue
            w, d, s2 = tr
            rest = right[1:]
            if d == 1:
                nxt.append(norm(s2, left + str(w), rest))
            else:
                if left.endswith("|") or left == "|":
                    # stepping left of the wall: an exit of the outer trip; the six cells after the wall
                    six = (str(w) + rest)
                    six = (left[1:] + six)[:6] if left != "|" else six[:6]
                    exits.add((s2, six.ljust(6, "u")))
                    continue
                if left == "":
                    nxt.append(norm(s2, "", "u" + str(w) + rest))
                else:
                    nxt.append(norm(s2, left[:-1], left[-1] + str(w) + rest))
    for x in nxt:
        if x not in seen:
            seen.add(x)
            todo.append(x)
    if len(seen) > MAXS:
        print("too many")
        break
print("states", len(seen), "halts", len(bad))
for b in bad[:5]:
    print("  halt", "ABCDEF"[b[0]], b[1], "[", b[2], "]")
ok = all(e in EXITS for e in exits)
print("exits", sorted(("ABCDEF"[s], c) for s, c in exits), "all known" if ok else "UNKNOWN EXITS")
