"""The wall-visit map of this machine as a recursion on words over X = 10, Y = 11, checked against the machine.

A *wall visit* is the head in F on a 0 with only 0s to its left; the tape to its right is then (almost always) a
word S of pairs X = 10 and Y = 11, and the next wall visit shows V(S) = G(S), one pair longer:

    G(Y^a X X U)     = X^a Y Y Y U
    G(Y^a X Y^k X U) = X^a Y G^k(Y Y U)          (k >= 1: the digit k passes k visits to the rest)
    G(Y^a)           = X^a Y Y                    (the head reaches the blank right end in B)

G is not defined when the word ends in X or in X Y^k: the head then reaches the blank right end in D (a
*right-end event*), and what follows is outside the recursion (it can change the parity of the pairs, leave blank
pairs inside the tape, and on some words it halts).

usage: python3 gmodel.py [STEPS]      tests G on random words and on the run from blank tape (default 3,000,000 steps)
"""
import os, random, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.machine import Machine

M = "1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA"
PAIR = {"X": (1, 0), "Y": (1, 1)}


def G(S):
    """The recursion, without recursion on the Python stack. None at a right-end event."""
    stack = []                    # frames [prefix, visits still to pass to the rest]
    cur = S
    while True:
        a = 0
        while a < len(cur) and cur[a] == "Y":
            a += 1
        if a == len(cur):
            val = "X" * a + "YY"
        else:
            k = 0
            while a + 1 + k < len(cur) and cur[a + 1 + k] == "Y":
                k += 1
            if a + 1 + k == len(cur):
                return None
            U = cur[a + k + 2:]
            if k == 0:
                val = "X" * a + "YYY" + U
            else:
                stack.append(["X" * a + "Y", k - 1])
                cur = "YY" + U
                continue
        # val = G(cur): give it to the frames waiting for it
        while stack and stack[-1][1] == 0:
            val = stack.pop()[0] + val
        if not stack:
            return val
        stack[-1][1] -= 1
        cur = val


def visit(m, S, max_steps=10**7):
    """Direct simulation of one wall visit of the word S. Returns the next word, or None if the visit halts or the
    next wall visit is not a word of X and Y with the same alignment."""
    tape = {}
    for i, ch in enumerate(S):
        tape[2 * i + 2], tape[2 * i + 3] = PAIR[ch]
    pos, st = 1, 5
    for _ in range(max_steps):
        tr = m.table[st][tape.get(pos, 0)]
        if tr is None:
            return None
        tape[pos], pos, st = tr[0], pos + tr[1], tr[2]
        if st == 5 and tape.get(pos, 0) == 0 and all(v == 0 for p, v in tape.items() if p < pos):
            return word(tape, pos)
    return None


def word(tape, wall):
    """The tape right of the wall cell as a word of X and Y (a trailing run of 1s of even length is Y's), or None."""
    hi = max([p for p, v in tape.items() if v] + [wall])
    cells = [tape.get(p, 0) for p in range(wall + 1, hi + 1)]
    if len(cells) % 2:
        cells.append(0)
    out = []
    for i in range(0, len(cells), 2):
        if cells[i] != 1:
            return None
        out.append("Y" if cells[i + 1] else "X")
    return "".join(out)


def main():
    steps = int(sys.argv[1]) if len(sys.argv) > 1 else 3000000
    m = Machine.parse(M)
    random.seed(1)
    n = ends = 0
    for _ in range(20000):
        S = "".join(random.choice("XY" if random.random() < 0.7 else "XXY") for _ in range(random.randint(0, 40)))
        g = G(S)
        if g is None:
            ends += 1
            continue
        n += 1
        assert visit(m, S) == g, S
    print("random words: G agrees with the machine on %d words (%d right-end events skipped)" % (n, ends))
    # the run from blank tape
    tape, pos, st = {}, 0, 0
    prev = None
    agree = skipped = total = 0
    lo = 0
    for k in range(1, steps + 1):
        tr = m.table[st][tape.get(pos, 0)]
        assert tr is not None
        tape[pos], pos, st = tr[0], pos + tr[1], tr[2]
        if pos < lo:
            lo = pos
        if st == 5 and pos == lo and tape.get(pos, 0) == 0:
            w = word(tape, pos)
            total += 1
            if prev is not None and prev[0] is not None and (prev[1] - pos) == 2:
                g = G(prev[0])
                if g is None:
                    skipped += 1
                else:
                    assert g == w, (k, prev[0], w, g)
                    agree += 1
            else:
                skipped += 1
            prev = (w, pos)
    print("run from blank tape, %d steps: %d wall visits, V = G checked at %d, %d not covered "
          "(right-end events and the visits around them)" % (steps, total, agree, skipped))


if __name__ == "__main__":
    main()
