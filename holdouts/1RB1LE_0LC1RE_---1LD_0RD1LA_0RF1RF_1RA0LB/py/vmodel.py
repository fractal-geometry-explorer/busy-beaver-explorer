"""The right-end visit map of this machine as a (partial) recursion on words of pairs, checked against the machine.

A *visit* is the head in A on the blank cell right of the tape.  Read the tape from the head leftwards in pairs of
cells: X is the pair `0 1`, Y is the pair `1 1` (so the word `Y Y X` is the tape `... 0 1 1 1 1 1 A>`).  The next visit
shows V(S), one pair longer:

    V(X U)        = Y Y U                 bounce
    V(Y X U)      = X X Y U
    V(Y Y X X U)  = X Y^4 U
    V(Y Y Y S)    = X X Y V(S)            three Y's pass the visit on
    V(Y Y X Y Y S) = X Y^4 V(S)           so does  Y Y X Y Y

Not covered (None): words starting `Y Y X Y X` (a second family of rules, not written down here) and visits that
reach the left end of the tape.

usage: python3 vmodel.py [STEPS]     tests V on random words and on the run from blank tape (default 3,000,000 steps)
"""
import os, random, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.machine import Machine

M = "1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB"


def V(S):
    out = []
    while True:
        if S.startswith("YYY") and len(S) > 3:
            out.append("XXY"); S = S[3:]
        elif S.startswith("YYXYY") and len(S) > 5:
            out.append("XYYYY"); S = S[5:]
        elif S.startswith("YYXX"):
            return "".join(out) + "XYYYY" + S[4:]
        elif S.startswith("YX"):
            return "".join(out) + "XXY" + S[2:]
        elif S.startswith("X"):
            return "".join(out) + "YY" + S[1:]
        else:
            return None


def word(tape, head):
    """The pairs left of the head, nearest first, as far as they are X = `0 1` or Y = `1 1` (cells in tape order)."""
    out = []
    p = head - 1
    while tape.get(p, 0) == 1:
        out.append("Y" if tape.get(p - 1, 0) else "X")
        p -= 2
    return "".join(out)


def visit(m, S, pad, max_steps=10**6):
    """Direct simulation of one visit of the word S followed (to the left) by the word pad. Returns the next word."""
    tape = {}
    p = -1
    for ch in S + pad:
        tape[p] = 1
        tape[p - 1] = 1 if ch == "Y" else 0
        p -= 2
    pos, st = 0, 0
    for k in range(max_steps):
        tr = m.table[st][tape.get(pos, 0)]
        if tr is None:
            return None
        tape[pos], pos, st = tr[0], pos + tr[1], tr[2]
        if st == 0 and tape.get(pos, 0) == 0 and all(v == 0 for q, v in tape.items() if q > pos):
            return word(tape, pos)
    return None


def main():
    steps = int(sys.argv[1]) if len(sys.argv) > 1 else 3000000
    m = Machine.parse(M)
    random.seed(1)
    n = skipped = 0
    pad = "X" * 12
    for _ in range(20000):
        S = "".join(random.choice("XY") for _ in range(random.randint(1, 30)))
        v = V(S + pad)
        if v is None:
            skipped += 1
            continue
        n += 1
        assert visit(m, S, pad) == v, S
    print("random words: V agrees with the machine on %d words (%d not covered)" % (n, skipped))
    tape, pos, st, hi = {}, 0, 0, 0
    prev = None
    agree = skipped = total = 0
    for k in range(1, steps + 1):
        tr = m.table[st][tape.get(pos, 0)]
        assert tr is not None
        tape[pos], pos, st = tr[0], pos + tr[1], tr[2]
        if pos > hi:
            hi = pos
        if st == 0 and pos == hi and tape.get(pos, 0) == 0:
            w = word(tape, pos)
            total += 1
            if prev is not None:
                v = V(prev)
                # covered only if the rules did not use the last pairs of the readable word
                if v is None or len(v) != len(prev) + 1 or len(w) < len(v):
                    skipped += 1
                else:
                    assert w[:len(v)] == v, (k, prev, w, v)
                    agree += 1
            prev = w
    print("run from blank tape, %d steps: %d visits, V checked at %d, %d not covered" % (steps, total, agree, skipped))


if __name__ == "__main__":
    main()
