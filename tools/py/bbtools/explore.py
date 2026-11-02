"""Look at a run from blank tape, for finding its macro structure.

usage:
  python3 -m bbtools.explore records MACHINE STEPS [K]        the tape each time the head reaches a new cell
  python3 -m bbtools.explore events MACHINE STEPS STATE SIDE  the tape each time the head, in STATE, is at the left
                                                             (SIDE L) or right (SIDE R) end of the visited cells
  python3 -m bbtools.explore blocks MACHINE STEPS STATE SIDE  the same events as lists of block lengths: the tape
                                                             between the ends split at runs of 0s, "ones-run:zeros-run"
  python3 -m bbtools.explore tokens MACHINE STEPS WORDS [SIDES [K]]
                                                             the tape as words, each time the head extends the visited
                                                             cells on a side other than the last extension's (SIDES L,
                                                             R or LR, default LR; at most K lines, default 200).  WORDS
                                                             names words of cells, `a=10,b=110`: the tape is read from
                                                             the left, longest word first, and run-length coded, a cell
                                                             no word matches printed as itself: `a^3 0 b a^2 1`.
  python3 -m bbtools.explore turns MACHINE FROM TO           every change of direction of the head between steps FROM
                                                             and TO: "STEPS S POS >|<", POS counted from the left end

Tapes are printed run-length coded (`1^5 0 C>1 1^2`, the head in state C on the cell after `>`).  For runs of
billions of steps use tools/c/tmrun (same output format for `records`).
"""
import sys

from .machine import Machine, Run, STATES, rle_cells


def events(m, steps, state, side):
    r = Run(m)
    while r.steps < steps:
        if not r.step():
            yield r, True
            return
        if r.state == state and ((side == "L" and r.head == r.tape.lo) or (side == "R" and r.head == r.tape.hi)):
            yield r, False


def blocks(cells):
    """[(ones, zeros), ...] for the cells, which start at a 1 or a 0 (then the first entry has ones = 0)."""
    out, i = [], 0
    while i < len(cells):
        j = i
        while j < len(cells) and cells[j] == 1:
            j += 1
        k = j
        while k < len(cells) and cells[k] == 0:
            k += 1
        out.append((j - i, k - j))
        i = k
    return out


def parse_words(spec):
    """`a=10,b=110` -> [("b", (1, 1, 0)), ("a", (1, 0))], longest first."""
    out = []
    for item in spec.split(","):
        name, cells = item.split("=")
        if not name or name in "01" or not cells or set(cells) - set("01"):
            raise ValueError(f"bad word {item!r}")
        out.append((name, tuple(int(c) for c in cells)))
    return sorted(out, key=lambda w: -len(w[1]))


def tokenize(cells, words):
    """The cells as a list of [token, count], read from the left, longest matching word first; a cell that starts
    no word is the token "0" or "1"."""
    out, i, n = [], 0, len(cells)
    while i < n:
        for name, w in words:
            if tuple(cells[i:i + len(w)]) == w:
                tok, i = name, i + len(w)
                break
        else:
            tok, i = str(cells[i]), i + 1
        if out and out[-1][0] == tok:
            out[-1][1] += 1
        else:
            out.append([tok, 1])
    return out


def token_str(toks):
    return " ".join(t if k == 1 else f"{t}^{k}" for t, k in toks)


def token_events(m, steps, words, sides="LR"):
    """Yield (run, side) each time the head extends the visited cells on the side other than the last extension's,
    for sides in `sides`; (run, "HALT") at a halt."""
    r, last = Run(m), None
    while r.steps < steps:
        lo, hi = r.tape.lo, r.tape.hi
        if not r.step():
            yield r, "HALT"
            return
        side = "L" if r.tape.lo < lo else "R" if r.tape.hi > hi else None
        if side and side != last:
            last = side
            if side in sides:
                yield r, side


def turns(m, start, stop):
    """Yield (steps, state, position from the left end, new direction) at every change of direction of the head
    between steps `start` and `stop`; the state is the one that made the turning move."""
    r = Run(m)
    while r.steps < start:
        if not r.step():
            return
    last = None
    while r.steps < stop:
        h, s = r.head, r.state
        if not r.step():
            return
        d = ">" if r.head > h else "<"
        if d != last:
            yield r.steps, s, h - r.tape.lo, d
            last = d


def main(argv):
    cmd, m, steps = argv[0], Machine.parse(argv[1]), int(argv[2])
    if cmd == "records":
        from .machine import records
        k = int(argv[3]) if len(argv) > 3 else 200
        for n, (t, side, r) in enumerate(records(m, steps)):
            if n >= k:
                break
            print(t, side, r.tape.hi - r.tape.lo, r.config_str())
    elif cmd in ("events", "blocks"):
        st, side = STATES.index(argv[3]), argv[4]
        for r, halted in events(m, steps, st, side):
            if halted:
                print(r.steps, "HALT", r.config_str())
                break
            if cmd == "events":
                print(r.steps, r.config_str())
            else:
                print(r.steps, " ".join(f"{a}:{b}" for a, b in blocks(r.tape.word())))
    elif cmd == "tokens":
        words = parse_words(argv[3])
        sides = argv[4] if len(argv) > 4 else "LR"
        k = int(argv[5]) if len(argv) > 5 else 200
        for n, (r, side) in enumerate(token_events(m, steps, words, sides)):
            if n >= k:
                break
            if side == "HALT":
                print(r.steps, "HALT", r.config_str())
                break
            print(r.steps, side, r.tape.hi - r.tape.lo, STATES[r.state], token_str(tokenize(r.tape.word(), words)))
    elif cmd == "turns":
        for t, s, pos, d in turns(m, steps, int(argv[3])):
            print(t, STATES[s], pos, d)
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
