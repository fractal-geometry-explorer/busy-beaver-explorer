"""What one bounce does to the frozen tape of 1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF, by brute force.

usage: python3 frozen.py [TRIALS]

A right turn: E reads 1, the zone (a prefix '' or '1', then letters u = 1110 / v = 1111) on its left, the frozen tape
(blocks of 1s b1 b2 b3 ... separated by single 0s, then blank) from the head on.  Run to the next right turn and
compare with the rules

  b1 >= 3:            the zone becomes T(w) and b1 drops by 2     (lean/Pascal.lean, `bounce`)
  b1 = 1:             halt                                      (lean/Pascal.lean, `halts_of_odd`)
  b1 = 2, b3 >= 2:    b1, b2 are absorbed, the next frozen block is b3 - 1
  b1 = 2, b3 = 1:     b3, b4 are absorbed too, and so on: the first b(2i+1) >= 2 drops by 1

for random zones of up to 8 letters and random frozen tapes of 6 blocks of 1 to 9 cells.  The zone never matters.
"""
import random
import sys

M = "1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF"
T = {}
for s, row in enumerate(M.split("_")):
    for b in range(2):
        x = row[3 * b:3 * b + 3]
        T[("ABCDEF"[s], b)] = None if x[0] == "-" else (int(x[0]), 1 if x[1] == "R" else -1, x[2])
ENC = {"1": "1110", "0": "1111"}


def bounce(p, w, frozen):
    z = p + "".join(ENC[x] for x in w)
    c = {i: int(ch) for i, ch in enumerate(z + frozen)}
    pos, st, last = len(z), "E", -1
    while True:
        b = c.get(pos, 0)
        tr = T[(st, b)]
        if tr is None:
            return None
        if tr[1] != last:
            if last == 1:
                return "".join(str(c.get(k, 0)) for k in range(pos, max(c) + 1))
            last = tr[1]
        c[pos] = tr[0]
        pos += tr[1]
        st = tr[2]


def predict(bl):
    if bl[0] >= 3:
        return [bl[0] - 2] + bl[1:]
    if bl[0] == 1:
        return None
    i = 2
    while i < len(bl) and bl[i] == 1:
        i += 2
    if i >= len(bl):
        return "end"
    return [bl[i] - 1] + bl[i + 1:]


def main():
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    rng = random.Random(1)
    ok = bad = skipped = 0
    for _ in range(trials):
        bl = [rng.randint(1, 9) for _ in range(6)]
        frozen = "0".join("1" * b for b in bl) + "0" * 12
        p = rng.choice(["", "1"])
        w = "".join(rng.choice("01") for _ in range(rng.randint(0, 8)))
        pr = predict(bl)
        if pr == "end":
            skipped += 1
            continue
        out = bounce(p, w, frozen)
        got = None if out is None else [len(x) for x in out.rstrip("0").split("0")]
        if got == pr:
            ok += 1
        else:
            bad += 1
            print("differs:", p, w, bl, got, pr)
    print(f"{ok} bounces as predicted, {bad} not, {skipped} skipped (absorption runs into the right end)")


if __name__ == "__main__":
    main()
