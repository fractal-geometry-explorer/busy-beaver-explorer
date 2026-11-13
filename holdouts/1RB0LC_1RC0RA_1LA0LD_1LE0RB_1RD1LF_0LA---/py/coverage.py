"""Which Lean theorem covers each round trip from a left-A record (head on a new leftmost cell in state A).

At each left-A record the tape, read from the head, is parsed greedily as units `(01)^b 0 0110`, then `(01)^a`, then a
frontier word (G1 `1`, G2 `00101`, K `001001`, H `0001`, X0 `0000`, X1 `001000`). The trip is covered by

* `covered-edge`: no unit: a `te*`/`se*` rule of `lean/FrontierRules.lean` (a whole round trip);
* `covered-units`: first unit b >= 2, all other units b >= 2: a `trip_tu*`/`trip_su*` theorem of `lean/Frontier.lean`;
* `T-regime`: the record lies inside a right-end regime (`py/phases.py`), whose trips are `trip` in `lean/Trip.lean`.

Everything else is printed by kind: `x<2` (first unit used up), `nopre-*` (a small frontier just after a unit, where
the rewrite starts a new unit), `unit b<2`, `word-*` (another frontier word).

usage: python3 holdouts/1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---/py/coverage.py 3e7   (about 25 minutes)
"""
import collections
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from snapshots import parse  # noqa: E402

M = "1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---"
# right-end regimes before 3e7 steps, from py/phases.py
T_REGIMES = ((2889, 7790), (35911, 263899), (7677126, 21453756))
UNIT = re.compile(r"((?:01)*)00110")
R01 = re.compile(r"(?:01)*")
WORDS = [("G1", "1"), ("G2", "00101"), ("K", "001001"), ("H", "0001"), ("X0", "0000"), ("X1", "001000")]
NOPRE = {("G1", 0), ("H", 0), ("H", 1), ("H", 2), ("X0", 0), ("X0", 1), ("X0", 2)}


def classify(s):
    i, bs = 0, []
    while True:
        m = UNIT.match(s, i)
        if not m:
            break
        bs.append(len(m.group(1)) // 2)
        i = m.end()
    m = R01.match(s, i)
    a, j = len(m.group(0)) // 2, m.end()
    w = next((n for n, x in WORDS if s.startswith(x, j)), None)
    if w is None:
        return "word-" + s[j:j + 6]
    if not bs:
        return "covered-edge"
    if bs[0] < 2:
        return "x<2"
    if min(bs[1:], default=9) < 2:
        return "unit b<2"
    if a < 3 and (w, a) in NOPRE:
        return f"nopre-{w}{a}"
    return "covered-units"


def main():
    n = int(float(sys.argv[1]))
    T = parse(M)
    tape = bytearray(1 << 23)
    h = lo = hi = 1 << 22
    s = 0
    cnt, first = collections.Counter(), {}
    tr01 = bytes.maketrans(b"\x00\x01", b"01")
    for k in range(1, n + 1):
        t = T[(s, tape[h])]
        if t is None:
            print("HALT", k)
            return
        w, d, s = t
        tape[h] = w
        h += d
        if h < lo:
            lo = h
            if s == 0:
                c = classify(bytes(tape[h:hi + 8]).translate(tr01).decode())
                if any(a <= k <= b for a, b in T_REGIMES):
                    c = "T-regime"
                cnt[c] += 1
                first.setdefault(c, k)
        elif h > hi:
            hi = h
    tot = sum(cnt.values())
    for c, v in cnt.most_common():
        print(f"{v:7d} {100 * v / tot:6.2f}%  {c}  (first at step {first[c]})")
    print("left-A records:", tot)


if __name__ == "__main__":
    main()
