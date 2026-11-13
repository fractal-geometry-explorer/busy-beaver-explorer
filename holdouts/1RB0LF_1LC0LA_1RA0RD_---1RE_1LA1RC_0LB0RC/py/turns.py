"""The tape of 1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC at its turns, written in blocks.

usage: python3 turns.py [STEPS] [EVERY]      (defaults 10^6 and 1)

Runs the machine from blank tape for STEPS steps and prints, at every EVERY-th time the head visits a new cell at
either end, the step, the side (L or R), the state, and the visited tape with the head marked, runs of the words in
WORDS shortened to `(w)^n`.
"""
import sys

M = "1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC"
WORDS = ['01', '011001', '010101']


def table(m):
    t = {}
    for s, part in enumerate(m.split("_")):
        for b in range(2):
            p = part[3 * b:3 * b + 3]
            t[(s, b)] = None if p[0] == "-" else (int(p[0]), 1 if p[1] == "R" else -1, ord(p[2]) - 65)
    return t


def blocks(s):
    out, i, lit = [], 0, ""
    while i < len(s):
        best = None
        for w in WORDS:
            n = 0
            while s.startswith(w, i + n * len(w)):
                n += 1
            if n >= 2 and (best is None or n * len(w) > best[1] * len(best[0])):
                best = (w, n)
        if best:
            if lit:
                out.append(lit)
                lit = ""
            out.append("(%s)^%d" % best)
            i += best[1] * len(best[0])
        else:
            lit += s[i]
            i += 1
    if lit:
        out.append(lit)
    return " ".join(out)


def main():
    steps = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 6
    every = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    t = table(M)
    tape, pos, st, lo, hi, k = {}, 0, 0, 0, 0, 0
    for n in range(1, steps + 1):
        b = tape.get(pos, 0)
        tr = t[(st, b)]
        if tr is None:
            print("HALT at step", n)
            return
        tape[pos] = tr[0]
        pos += tr[1]
        st = tr[2]
        side = None
        if pos < lo:
            lo, side = pos, "L"
        elif pos > hi:
            hi, side = pos, "R"
        if side:
            k += 1
            if k % every == 0:
                s = "".join(str(tape.get(i, 0)) for i in range(lo, hi + 1))
                h = pos - lo
                print(n, side, blocks(s[:h]), "ABCDEF"[st] + ">", blocks(s[h:]))


if __name__ == "__main__":
    main()
