"""Look at how this machine sweeps: one-block behaviour, words crossed whole, the way back from a halt, and the tape.

usage (from the repo root):  python3 holdouts/MACHINE/py/passes.py [blocks|cross|back|tape] [ARGS]

  blocks K        for every state and every word of K cells, entered from the left (moving right) or from the right
                  (moving left): the side the head leaves by, its state, the word left behind, the steps
  cross           which states cross each rotation of the background words whole (shift rules), in which direction,
                  and what each copy becomes (uses tools/py/bbtools/symtm.py, as py/rules.py does)
  back D          every chain of D steps that ends in the halting transition (cells as they are before each step;
                  `[S x]` is the head in state S reading x, `.` a cell that does not matter)
  tape STEPS N    the tape, run-length coded, the first N times the head reaches the left end after STEPS steps
"""
import itertools
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
M = os.path.basename(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))

WORDS = ['1010100', '0101101', '100']


def parse(m):
    t = {}
    for s, part in enumerate(m.split("_")):
        for r in range(2):
            x = part[3 * r:3 * r + 3]
            t[(s, r)] = None if x[2] == "-" else (int(x[0]), 1 if x[1] == "R" else -1, ord(x[2]) - 65)
    return t


T = parse(M)


def runblock(st, w, side):
    t = list(w)
    p = 0 if side == "L" else len(t) - 1
    n = 0
    while 0 <= p < len(t):
        tr = T[(st, t[p])]
        if tr is None:
            return ("halt", "", "".join(map(str, t)), n)
        t[p] = tr[0]
        p += tr[1]
        st = tr[2]
        n += 1
        if n > 1000:
            return ("loop", "", "", n)
    return ("R" if p >= len(t) else "L", "ABCDEF"[st], "".join(map(str, t)), n)


def blocks(k):
    for side, name in (("L", "moving right (entering at the left cell)"), ("R", "moving left (entering at the right cell)")):
        print(name)
        for s in range(6):
            row = []
            for w in itertools.product([0, 1], repeat=k):
                r = runblock(s, w, side)
                row.append("%s:%s" % ("".join(map(str, w)), "/".join(map(str, r))))
            print("  " + "ABCDEF"[s], "  ".join(row))


def cross():
    from bbtools import symtm
    from bbtools.symtm import Config, Ctx, run
    m = symtm.Machine.parse(M)

    def attempt(start, side):
        cfg = Config.parse(start)

        def stop(c):
            if side == "r":
                return isinstance(c.right[0], Ctx) and not c.steps.is_zero()
            return len(c.left) == 1 and isinstance(c.left[0], Ctx) and not c.steps.is_zero()
        try:
            fin = run(m, cfg, stop, max_moves=200)
        except Exception:
            return None
        return fin if fin.steps.vars() else None

    for w0 in WORDS:
        for i in range(len(w0)):
            w = w0[i:] + w0[:i]
            for q in "ABCDEF":
                s = f"L {q}> ({w})^n R"
                f = attempt(s, "r")
                if f is not None and symtm.STATES[f.state] == q:
                    print("right", s, "==>", f, " steps", f.steps)
                for u in "01":
                    s = f"L ({w})^n {q}> {u} R"
                    f = attempt(s, "l")
                    if f is not None:
                        print("left ", s, "==>", f, " steps", f.steps)


def back(depth):
    def show(node):
        st, p, c = node
        lo, hi = min(min(c), p), max(max(c), p)
        return "".join(("[%s%s]" % ("ABCDEF"[st], c[x]) if x == p else (str(c[x]) if x in c else "."))
                       for x in range(lo, hi + 1))
    frontier = [((s, 0, {0: b}), [show((s, 0, {0: b}))]) for (s, b), tr in T.items() if tr is None]
    for d in range(depth):
        nf = []
        for (st, p, cells), h in frontier:
            for (s, b), tr in T.items():
                if tr is None or tr[2] != st:
                    continue
                q = p - tr[1]
                if q in cells and cells[q] != tr[0]:
                    continue
                c = dict(cells)
                c[q] = b
                nf.append(((s, q, c), h + [show((s, q, c))]))
        frontier = nf
        print("depth", d + 1, "chains", len(frontier))
    for _, h in frontier:
        print("  ", " <- ".join(h))


def rle(s):
    out, i = [], 0
    while i < len(s):
        best = (1, 1)
        for w in range(1, 13):
            k = 1
            while s[i + k * w:i + (k + 1) * w] == s[i:i + w]:
                k += 1
            if k >= 3 and k * w > best[0] * best[1]:
                best = (k, w)
        k, w = best
        out.append("(%s)^%d" % (s[i:i + w], k) if k >= 3 else s[i])
        i += k * w if k >= 3 else 1
    return " ".join(out)


def tape(steps, n):
    tp = bytearray(1 << 22)
    p = lo = hi = len(tp) // 2
    st, away, shown = 0, False, 0
    for k in range(1, steps + 10 ** 9):
        tr = T[(st, tp[p])]
        if tr is None:
            print("halt", k)
            return
        tp[p] = tr[0]
        p += tr[1]
        st = tr[2]
        lo, hi = min(lo, p), max(hi, p)
        away = away or p > lo + 8
        if p == lo and away:
            away = False
            if k >= steps:
                print(k, "ABCDEF"[st], rle("".join("01"[c] for c in tp[lo:hi + 1])))
                shown += 1
                if shown >= n:
                    return


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "blocks"
    if cmd == "blocks":
        blocks(int(sys.argv[2]) if len(sys.argv) > 2 else 2)
    elif cmd == "cross":
        cross()
    elif cmd == "back":
        back(int(sys.argv[2]) if len(sys.argv) > 2 else 4)
    elif cmd == "tape":
        tape(int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 6, int(sys.argv[3]) if len(sys.argv) > 3 else 3)
