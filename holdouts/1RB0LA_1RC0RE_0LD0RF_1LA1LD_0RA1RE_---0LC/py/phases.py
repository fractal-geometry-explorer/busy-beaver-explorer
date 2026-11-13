"""The regimes of 1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC from blank tape.

usage: python3 holdouts/1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC/py/phases.py [STEPS]   (default 300,000,000)

At every new left end of the tape in state A the tape is matched against the three regimes of lean/Phase.lean (samples
half-way through a round trip, which start 0 0 1 1 1 1 1, are skipped):
  Q  a R      (01110)^a 0 1111 (001)^a (01111)^b TAIL
  Z  a c d    (01110)^a 0 1111 (001)^c 11001001111 (001)^d 11001
and one line is printed per stretch of samples of the same regime (other samples in between are ignored; a\nstretch ends when the regime changes or its first parameter drops): its first and last parameters.
"""
import re
import sys

M = "1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC"
PAT = [
    ("Q", re.compile(r"^((?:01110)*)01111((?:001)*)((?:01111)*)(.*)$")),
]
ZP = re.compile(r"^((?:01110)*)01111((?:001)*)11001001111((?:001)*)11001$")


def classify(cells):
    m = ZP.match(cells)
    if m:
        return "Z", (len(m.group(1)) // 5, len(m.group(2)) // 3, len(m.group(3)) // 3)
    m = PAT[0][1].match(cells)
    if m and len(m.group(1)) // 5 == len(m.group(2)) // 3 and m.group(3):
        return "Q", (len(m.group(1)) // 5, len(m.group(3)) // 5)
    if cells.startswith("0011111"):
        return "half", None     # the same round trip seen half-way (the left end is visited twice per trip)
    return None, None


def table(m):
    t = []
    for g in m.split("_"):
        row = []
        for b in (0, 1):
            x = g[3 * b:3 * b + 3]
            row.append(None if x[2] == "-" else (int(x[0]), 1 if x[1] == "R" else -1, "ABCDEF".index(x[2])))
        t.append(row)
    return t


def run(steps):
    t = table(M)
    size = 1 << 17
    tape = bytearray(size)
    h = lo = hi = size // 2
    s = 0
    cur = [None, 0, None, 0, None]
    for k in range(1, steps + 1):
        tr = t[s][tape[h]]
        if tr is None:
            print("HALT", k)
            return
        w, d, s = tr
        tape[h] = w
        h += d
        if h < lo:
            lo = h
            if s == 0:
                cells = tape[lo:hi + 1].decode("latin1").translate({0: "0", 1: "1"}).rstrip("0")
                kind, par = classify(cells)
                if kind in ("half", None):
                    continue
                if kind != cur[0] or par[0] < cur[4][0]:
                    if cur and cur[0]:
                        print(f"{cur[0]:<3} steps {cur[1]:>12,} .. {cur[3]:>12,}  {cur[2]} .. {cur[4]}")
                    cur = [kind, k, par, k, par]
                else:
                    cur[3], cur[4] = k, par
        elif h > hi:
            hi = h
        if h < 8 or h > size - 8:
            raise SystemExit("tape too small")
    if cur and cur[0]:
        print(f"{cur[0]:<3} steps {cur[1]:>12,} .. {cur[3]:>12,}  {cur[2]} .. {cur[4]}  (still running)")


if __name__ == "__main__":
    run(int(float(sys.argv[1])) if len(sys.argv) > 1 else 300_000_000)
