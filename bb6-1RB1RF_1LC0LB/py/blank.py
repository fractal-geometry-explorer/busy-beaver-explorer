"""The run of 1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE--- from blank tape, with the shared reference simulator.

usage:
  python3 py/blank.py summary STEPS          halted or not, steps, ones, the number of visited cells
  python3 py/blank.py left STEPS [K]         the tape as words a = 10, b = 110 each time the head extends the tape
                                             on the left (at most K lines): "STEPS L WIDTH STATE words"
  python3 py/blank.py turns FROM TO          the tape as words at every change of direction of the head, the head
                                             shown as [S] in front of the cell it reads
  python3 py/blank.py rare STEPS             how often each transition is used (A, D1, E0 and F are rare)

The tape is made of pairs `10` (the word a) with single extra 0s between blocks of them; see notes/LAB_NOTES.md.
A halt needs `E>0 1 1` (lean/Blank.lean, `halt_from_e011`).  For runs of billions of steps use the C programs:
gcc -O2 -o tokrun tools/c/tokrun.c && ./tokrun MACHINE 2000000000 a=10,b=110 L 1000 prints what `left` prints.
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools", "py"))

from bbtools.explore import parse_words, token_events, token_str, tokenize  # noqa: E402
from bbtools.machine import Machine, Run, STATES  # noqa: E402

M = "1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---"
MACHINE = Machine.parse(M)
WORDS = parse_words("a=10,b=110")
A, B, C, D, E, F = range(6)


def summary(steps):
    """(halted, steps, ones, width) of the run from blank tape, at most `steps` steps."""
    r = Run(MACHINE)
    h = r.run(steps)
    return h, r.steps, r.ones(), r.tape.hi - r.tape.lo + 1


def words(cells):
    return token_str(tokenize(cells, WORDS))


def left_events(steps):
    """Yield (steps, width, state, words) each time the head extends the tape on the left after it last extended it
    on the right; (steps, None, None, "HALT") at a halt."""
    for r, side in token_events(MACHINE, steps, WORDS, "L"):
        if side == "HALT":
            yield r.steps, None, None, "HALT"
            return
        yield r.steps, r.tape.hi - r.tape.lo, STATES[r.state], words(r.tape.word())


def blocks(tape_words):
    """The block list of a left event's words when they have the plain form `0^2 a^n1 0 a^n2 ... 0 a^nk 1`, else
    None: [n1, ..., nk]."""
    t = tape_words.split()
    if t[:1] != ["0^2"] or t[-1:] != ["1"]:
        return None
    out, expect_a = [], True
    for w in t[1:-1]:
        if expect_a and (w == "a" or w.startswith("a^")):
            out.append(1 if w == "a" else int(w[2:]))
            expect_a = False
        elif not expect_a and w == "0":
            expect_a = True
        else:
            return None
    return out if not expect_a else None


def turn_tapes(start, stop):
    """Yield (steps, state, direction, words left of the head, words from the head on) at every change of
    direction between steps `start` and `stop`."""
    r = Run(MACHINE)
    while r.steps < start and r.step():
        pass
    last = None
    while r.steps < stop:
        h = r.head
        if not r.step():
            return
        d = ">" if r.head > h else "<"
        if d != last:
            last = d
            w, i = r.tape.word(), r.head - r.tape.lo
            yield r.steps, STATES[r.state], d, words(w[:i]), words(w[i:])


def rare(steps):
    """{(state, read): count} over the first `steps` steps."""
    r, n = Run(MACHINE), {}
    while r.steps < steps:
        key = (STATES[r.state], r.tape.get(r.head))
        n[key] = n.get(key, 0) + 1
        if not r.step():
            break
    return n


def main(argv):
    cmd = argv[0] if argv else ""
    if cmd == "summary":
        h, t, ones, w = summary(int(argv[1]))
        print(f"{'halted' if h else 'running'} steps={t} ones={ones} cells={w}")
    elif cmd == "left":
        k = int(argv[2]) if len(argv) > 2 else 200
        for n, (t, w, s, ws) in enumerate(left_events(int(argv[1]))):
            if n >= k:
                break
            print(t, "HALT" if w is None else f"L {w} {s} {ws}")
    elif cmd == "turns":
        for t, s, d, lw, rw in turn_tapes(int(argv[1]), int(argv[2])):
            print(t, d, lw, f"[{s}]", rw)
    elif cmd == "rare":
        for (s, y), c in sorted(rare(int(argv[1])).items()):
            print(f"{s}{y} {c}")
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
