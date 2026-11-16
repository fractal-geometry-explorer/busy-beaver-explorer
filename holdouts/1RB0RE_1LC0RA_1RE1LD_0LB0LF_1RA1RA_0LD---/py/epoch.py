"""The walker law of 1RB0RE_1LC0RA_1RE1LD_0LB0LF_1RA1RA_0LD--- inside an epoch, checked against the machine, and run
far ahead.

Events.  A *round* ends each time the head, in state A, stands on the first blank cell right of everything written
(`tmrun MACHINE STEPS at A R`).  At those moments the tape reads

    1 1 1 0 0  u_1 u_2 ... u_k  X  (1 0)^N 1

with u_i six-cell *units* `1 x y 1 0 0`, written as digits by their middle bits xy:
    '1' = 1 00 100,  '0' = 1 01 100,  '2' = 1 10 100,  '3' = 1 11 100,
X a fixed stretch of other words (unchanged during an epoch) and a tail of N single 1s (the fast counter, N grows by
one per round).  Between two rebuilds (an *epoch*) every round changes the digits by one local operation at a
*walker*, which moves left, and the length of a round is twice the previous one plus a constant that depends only on
the operation:

  phase 1 (walker W at digit p, building 2s):
     a   '0' -> '1' at p                                        c = +16
     b   '1' -> '2' at p, then W moves to p - 1                 c = +4
     a'  if the digit at p is a '1' that was there before:
         '1' -> '3' at p, phase 2 starts at p                   c = +18
     at the front (no digit left of the walker) the leader 1 1 1 0 0 becomes 1 0 1 0 0   c = +16
         (seen once, epoch 3, round end 348,360,095,421); the round after that is a rebuild
  phase 2 (carry K at digit p holding a '3'):
     a   digit p-1 '0' -> '1' and digit p '3' -> '0'            c = +14
     b   digit p-1 '1' -> '3', K moves to p - 1                 c = -10
     at the front the leader 1 1 1 0 0 plays the role of digit p-1 in step a (it becomes 1 0 1 0 0, c = +14);
     the round after that is a *rebuild* (not modelled: the tail is absorbed into a new, longer unit list).

  T(next round) = 2 T(this round) + c(operation of the next round)

So within an epoch the step count of every round is a closed form: T_r = 2^r T_0 + sum_i 2^(r-i) c_i.

This is observed (`check` compares every round of epochs 2 and 3 with the machine), not proved.

usage: python3 epoch.py check FILE      FILE = output of `tmrun MACHINE STEPS at A R 5000`; every predicted round
                                        against the machine's, from the first regular round of each epoch on
       python3 epoch.py ahead           epoch 2 and 3 run to the end of their walks by the law (steps of each round)
"""
import re
import sys

UNIT = {"101100": "0", "100100": "1", "110100": "2", "111100": "3"}
CODE = {v: k for k, v in UNIT.items()}


def parse(cells):
    """cells (a string, trailing blanks stripped) -> (digits, rest, N) or None."""
    s = cells.strip("0")
    if not (s.startswith("11100") or s.startswith("10100")):
        return None
    i, d = 5, []
    while i + 6 <= len(s) and s[i:i + 6] in UNIT:
        d.append(UNIT[s[i:i + 6]]); i += 6
    m = re.fullmatch(r"(.*?)((?:10)*1)", s[i:])
    if not m:
        return None
    return "".join(d), m.group(1), (len(m.group(2)) + 1) // 2


class Walk:
    """The walker state: digits, phase (1 or 2), position, sub-step ('a' or 'b'), last round length, step."""

    def __init__(self, digits, phase, pos, sub, T, step, fresh=False):
        self.d, self.phase, self.p, self.sub, self.T, self.step = list(digits), phase, pos, sub, T, step
        self.fresh = fresh        # in phase 1: the '1' at p was written by the walker (so 'b' applies)
        self.done = False         # the leader has been changed: the next round is a rebuild

    def next(self):
        d, p = self.d, self.p
        if self.phase == 1:
            if self.sub == "a":
                if p < 0:
                    # the walker has reached the leader 1 1 1 0 0: it becomes 1 0 1 0 0 (seen once, epoch 3 at step
                    # 348,360,095,421); the round after is a rebuild
                    if self.done:
                        raise ValueError("rebuild (not modelled)")
                    c = 16; self.done = True
                    self.T = 2 * self.T + c
                    self.step += self.T
                    return "".join(d), c
                if d[p] == "0":
                    d[p] = "1"; c = 16; self.sub = "b"; self.fresh = True
                elif d[p] == "1":
                    d[p] = "3"; c = 18; self.phase, self.sub = 2, "a"
                else:
                    raise ValueError(f"phase 1 at digit {d[p]!r}")
            else:
                assert d[p] == "1" and self.fresh
                d[p] = "2"; c = 4; self.p -= 1; self.sub = "a"; self.fresh = False
        else:
            if self.done:
                raise ValueError("rebuild (not modelled)")
            if self.sub == "a":
                assert d[p] == "3"
                if p == 0:
                    d[p] = "0"; c = 14; self.done = True
                else:
                    assert d[p - 1] == "0", (d, p)
                    d[p - 1] = "1"; d[p] = "0"; c = 14; self.sub = "b"
            else:
                assert d[p - 1] == "1"
                d[p - 1] = "3"; c = -10; self.p -= 1; self.sub = "a"
        self.T = 2 * self.T + c
        self.step += self.T
        return "".join(d), c


def rounds_from_file(path):
    from_line = []
    for line in open(path):
        p = line.split()
        if not p or p[0] in ("running", "halted"):
            continue
        cells = []
        for tk in p[1:]:
            if ">" in tk:
                cells.append(tk[-1]); continue
            a, _, e = tk.partition("^")
            cells += [a] * (int(e) if e else 1)
        from_line.append((int(p[0]), parse("".join(cells))))
    return from_line


# the first regular round of the epochs seen in direct runs: (step, round length, digits, phase, pos, sub, fresh)
# (only the digits left of the walker's start are listed; the digits right of it stay fixed during the epoch).
# epoch 2: digits 0000100000|30 at step 40,509,722, walker at digit 9 (0-based); epoch 3: 000001000|1220 at step
# 12,398,695,221, the walker has just written the '1' at digit 5.
STARTS = [
    (40509722, 2926, "0000100000", 1, 9, "a", False),
    (12398695221, 41020920, "000001000", 1, 5, "b", True),
]


def check(path):
    obs = rounds_from_file(path)
    ok = bad = 0
    for step0, T0, dig, ph, pos, sub, fresh in STARTS:
        idx = [i for i, (s, _) in enumerate(obs) if s == step0]
        if not idx:
            print("start", step0, "not in the file"); continue
        i = idx[0]
        w = Walk(dig, ph, pos, sub, T0, step0, fresh)
        width = len(dig)
        while i + 1 < len(obs):
            i += 1
            s, cfg = obs[i]
            if cfg is None:
                break
            try:
                dg, c = w.next()
            except ValueError as e:
                print("  law stops:", e); break
            good = (s == w.step and cfg[0][:width] == dg)
            ok += good; bad += not good
            print(f"  {s:>16,}  {cfg[0]:<14} N={cfg[2]:<3} predicted {w.step:>16,} {dg:<12} c={c:+d}", "" if good else "MISMATCH")
            if w.done:
                break
    print("rounds checked:", ok, "mismatches:", bad)


def ahead():
    for step0, T0, dig, ph, pos, sub, fresh in STARTS:
        w = Walk(dig, ph, pos, sub, T0, step0, fresh)
        r = 0
        print("epoch from step", f"{step0:,}")
        while True:
            try:
                dg, c = w.next()
            except ValueError as e:
                print("  stops:", e); break
            r += 1
            print(f"  round {r:>3}  {dg}  c={c:+d}  ends at step {w.step:,}")
            if w.done:
                print("  next round is a rebuild"); break


if __name__ == "__main__":
    if len(sys.argv) >= 3 and sys.argv[1] == "check":
        check(sys.argv[2])
    elif len(sys.argv) >= 2 and sys.argv[1] == "ahead":
        ahead()
    else:
        sys.exit(__doc__)
