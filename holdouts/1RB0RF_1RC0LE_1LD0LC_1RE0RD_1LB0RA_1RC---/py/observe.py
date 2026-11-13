"""Look at the run of 1RB0RF_1RC0LE_1LD0LC_1RE0RD_1LB0RA_1RC--- from blank tape: the observations quoted in README.md.

usage (from the repository root):
  python3 holdouts/1RB0RF_1RC0LE_1LD0LC_1RE0RD_1LB0RA_1RC---/py/observe.py turns STEPS [L|R]    the tape at each turn on that side (head at that end of the
                                                           visited cells, about to turn), run-length coded
  python3 holdouts/1RB0RF_1RC0LE_1LD0LC_1RE0RD_1LB0RA_1RC---/py/observe.py blocks STEPS [L|R]   the same tapes as lengths of the blocks of ones
  python3 holdouts/1RB0RF_1RC0LE_1LD0LC_1RE0RD_1LB0RA_1RC---/py/observe.py shift STEPS [L|R]    the stretches (150 cells or more) of the last turn's tape that
                                                           equal the previous turn's tape moved by some number of cells
  python3 holdouts/1RB0RF_1RC0LE_1LD0LC_1RE0RD_1LB0RA_1RC---/py/observe.py path FROM TO       the turning points of the head between two steps (a turn
                                                           counts once the head has moved 20 cells back), as cell
                                                           positions relative to the start
  python3 holdouts/1RB0RF_1RC0LE_1LD0LC_1RE0RD_1LB0RA_1RC---/py/observe.py prehalt STEPS        how often the machine enters the halting state, and from
                                                           where (the C version c/prehalt.c does 10^9 steps quickly)
"""
import sys

M = "1RB0RF_1RC0LE_1LD0LC_1RE0RD_1LB0RA_1RC---"


def table(m):
    t = {}
    for s, part in enumerate(m.split("_")):
        for r in range(2):
            x = part[3 * r:3 * r + 3]
            t[(s, r)] = None if x[2] == "-" else (int(x[0]), 1 if x[1] == "R" else -1, ord(x[2]) - 65)
    return t


def run(steps, on_extend, n=1 << 22):
    t = table(M)
    tab = [[t[(s, r)] for r in range(2)] for s in range(6)]
    tape = bytearray(n)
    p = lo = hi = n // 2
    st = 0
    for k in range(1, steps + 1):
        tr = tab[st][tape[p]]
        if tr is None:
            print("halted at step", k)
            return
        tape[p] = tr[0]
        p += tr[1]
        st = tr[2]
        if p < lo or p > hi:
            lo, hi = min(lo, p), max(hi, p)
            on_extend(k, p, lo, hi, st, tape)


def turns(steps, side):
    """(step, lo, tape bytes, state) at each turn on `side`: the last extension on that side before one on the other."""
    out, last = [], [None]

    def cb(k, p, lo, hi, st, tape):
        s = "L" if p == lo else "R"
        if last[0] and last[0][0] != s and last[0][0] == side:
            out.append(last[0][1:])
        last[0] = (s, k, lo, bytes(tape[lo:hi + 1]), st)
    run(steps, cb)
    return out


def rl(s):
    o, i = [], 0
    while i < len(s):
        j = i
        while j < len(s) and s[j] == s[i]:
            j += 1
        o.append(str(s[i]) + ("" if j - i == 1 else "^%d" % (j - i)))
        i = j
    return " ".join(o)


def main():
    cmd, steps = sys.argv[1], int(sys.argv[2])
    side = sys.argv[3] if len(sys.argv) > 3 else "L"
    if cmd in ("turns", "blocks"):
        for k, lo, s, st in turns(steps, side):
            if cmd == "turns":
                print(k, "ABCDEF"[st], len(s), rl(s))
            else:
                t = "".join("01"[c] for c in s).strip("0")
                print(k, len(s), " ".join(str(len(b)) for b in t.split("0") if b))
    elif cmd == "shift":
        ts = turns(steps, side)
        (k0, lo0, s, _), (k1, lo1, s1, _) = ts[-1], ts[-2]
        print("turn at step", k0, "width", len(s), "; previous at", k1, "width", len(s1))
        segs = []
        for d in range(-400, 401):
            run_ = 0
            for x in range(len(s) + 1):
                y = x + lo0 + d - lo1
                if x < len(s) and 0 <= y < len(s1) and s[x] == s1[y]:
                    run_ += 1
                else:
                    if run_ >= 150:
                        segs.append((run_, x - run_, x, d))
                    run_ = 0
        keep = []
        for r, a, b, d in sorted(segs, key=lambda t: (-t[0], abs(t[3]))):
            if not any(min(b, b2) - max(a, a2) > 0.5 * (b - a) for _, a2, b2, _ in keep):
                keep.append((r, a, b, d))
        for r, a, b, d in sorted(keep, key=lambda t: t[1]):
            print("  cells %d..%d equal the previous tape moved %d cells %s" % (a, b, abs(d), "left" if d > 0 else "right"))
    elif cmd == "path":
        t = table(M)
        tab = [[t[(s, r)] for r in range(2)] for s in range(6)]
        n = 1 << 22
        tape = bytearray(n)
        p = n // 2
        st = 0
        end = int(sys.argv[3])
        d, ext, ek = 1, p, 0
        for k in range(1, end + 1):
            tr = tab[st][tape[p]]
            if tr is None:
                print("halted at step", k)
                return
            tape[p] = tr[0]
            p += tr[1]
            st = tr[2]
            if (d > 0 and p > ext) or (d < 0 and p < ext):
                ext, ek = p, k
            elif abs(p - ext) > 20:
                if ek >= steps:
                    print(ek, ext - n // 2, "max" if d > 0 else "min")
                d, ext, ek = -d, p, k
    elif cmd == "prehalt":
        t = table(M)
        hs, hb = next(k for k, v in t.items() if v is None)
        cnt = {}
        tab = [[t[(s, r)] for r in range(2)] for s in range(6)]
        tape = bytearray(1 << 22)
        p = 1 << 21
        st = 0
        for k in range(steps):
            r = tape[p]
            tr = tab[st][r]
            if tr is None:
                print("halted at step", k + 1)
                return
            if tr[2] == hs:
                cnt["ABCDEF"[st] + str(r)] = cnt.get("ABCDEF"[st] + str(r), 0) + 1
            tape[p] = tr[0]
            p += tr[1]
            st = tr[2]
        print("halting transition", "ABCDEF"[hs] + str(hb), "; entries into", "ABCDEF"[hs], "from:", cnt)


if __name__ == "__main__":
    main()
