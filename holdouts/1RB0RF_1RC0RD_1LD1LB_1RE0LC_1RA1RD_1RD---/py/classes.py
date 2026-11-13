"""Which tapes near the real run halt?  Three experiments on the block-level law (py/law.py), in the reference
orientation.  A tape is given by its gap list at a block-end turn; the law starts either in C with open block 2 or
in D with open block 3, on a gap 1, with the list after it (the two starts the real run alternates between).

usage (from the repository root):
  python3 holdouts/MACHINE/py/classes.py small [MAXLEN]   every gap list over {1, 2, 4} up to MAXLEN gaps (default 8)
  python3 holdouts/MACHINE/py/classes.py factors [N]      N random lists over {1, 2, 4} without the factors 4 4, 1 4, 1 2 4
  python3 holdouts/MACHINE/py/classes.py words [N]        N random lists made of the words S = 1, P = 2 2, Q = 4 2
                                                          without S directly before Q, in both alignments
A trial "halts" if the law reaches state F on a gap 0 within the budget of rules; "unusual" counts the rules the
run from blank tape never uses inside the tape (c_turn5, d_turn3, d_turn4, d_gap0, d_gap2).
"""
import itertools
import os
import random
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from law import Law, Halt  # noqa: E402

BAD = [(4, 4), (1, 4), (1, 2, 4)]
UNUSUAL = ("c_turn5", "d_turn3", "d_turn4", "d_gap0", "d_gap2")
WORDS = {"S": [1], "P": [2, 2], "Q": [4, 2]}


def has(w, f):
    return any(tuple(w[i:i + len(f)]) == f for i in range(len(w) - len(f) + 1))


def run(start, gaps, budget, odd=None):
    m = Law(0, 0)
    m.G = list(gaps)[::-1]
    m.q, m.o, m.g = (("C", 2, 1) if start == "C" else ("D", 3, 1))
    try:
        for _ in range(budget):
            m.step()
            if odd is not None and m.rule in UNUSUAL and m.z != float("inf"):
                odd[m.rule] += 1
    except Halt:
        return True
    return False


def small(maxlen, budget=4000):
    halting, total = [], 0
    for n in range(1, maxlen + 1):
        for w in itertools.product((1, 2, 4), repeat=n):
            for st in "CD":
                total += 1
                if run(st, w, budget):
                    halting.append((st, w))
    rest = [h for h in halting if not any(has(h[1], f) for f in BAD)]
    print(f"{total} tapes (gap lists over 1, 2, 4 of length <= {maxlen}, two starts), {budget} rules each: {len(halting)} halt")
    print(f"  halting ones that contain none of the factors 4 4, 1 4, 1 2 4: {len(rest)}")
    for st, w in halting[:6]:
        print(f"  e.g. start {st}, gaps {' '.join(map(str, w))}")


def factors(n, budget=30000):
    random.seed(11)
    halts, odd = 0, Counter()
    for _ in range(n):
        w = []
        size = random.randint(5, 120)
        while len(w) < size:
            w.append(random.choice((1, 2, 2, 2, 4)))
            if any(tuple(w[-len(f):]) == f for f in BAD):
                w.pop()
        for st in "CD":
            halts += run(st, w, budget, odd)
    print(f"{2 * n} random tapes over 1, 2, 4 without the factors 4 4, 1 4, 1 2 4, {budget} rules each: {halts} halt; unusual rules {dict(odd)}")


def words(n, budget=20000):
    random.seed(5)
    for cls, text in (("A", "S always followed by P"), ("B", "S never directly before Q")):
        halts, odd, runs = 0, Counter(), 0
        for _ in range(n):
            w = ""
            size = random.randint(3, 80)
            while len(w) < size:
                c = random.choice("SPPQ")
                if c == "Q" and w.endswith("S"):
                    continue
                if cls == "A" and c != "P" and w.endswith("S"):
                    continue
                w += c
            if cls == "A" and w.endswith("S"):
                w += "P"
            for st in "CD":
                for lead in (0, 1):
                    runs += 1
                    halts += run(st, [2] * lead + [g for x in w for g in WORDS[x]], budget, odd)
        print(f"words S, P, Q, {text}: {runs} runs (two starts, two alignments), {budget} rules each: {halts} halt; unusual rules {dict(odd)}")


if __name__ == "__main__":
    a = sys.argv[1:]
    cmd = a[0] if a else "small"
    if cmd == "small":
        small(int(a[1]) if len(a) > 1 else 8)
    elif cmd == "factors":
        factors(int(a[1]) if len(a) > 1 else 400)
    elif cmd == "words":
        words(int(a[1]) if len(a) > 1 else 300)
    else:
        print(__doc__)
