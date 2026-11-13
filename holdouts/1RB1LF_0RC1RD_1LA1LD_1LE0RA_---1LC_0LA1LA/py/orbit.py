"""Iterate the map of lean/Map.lean (`mapc`) from (74, 30), the round start at step 6,998.

usage: python3 orbit.py [N] [--check]

`mapc` is the same function as in Map.lean.  With --check, the first rounds are also compared with a direct
simulation of the machine (the round starts `A>0 1^a 0 1^c`, from tools/py/bbtools/machine.py).
Prints every 10% of the way the size of c (bits), and how close c - a ever came to the halting differences.
"""
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))

M = "1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA"


def mapc(a, c):
    """'halt', 'small' or (a', c'), as Map.lean's mapc."""
    if a % 2 == 1 or a < 4:
        return "small"
    if c % 2 == 0:
        if c < 18 or a < 6:
            return "small"
        if c <= a + 8:
            return (a + 12 - c, 3 * c - 6)
        if c <= a + 12:
            return "halt"
        return (c - a - 10, 3 * a + 27)
    if c < 5:
        return "small"
    if c + 5 <= a:
        return (a - c - 1, 3 * c + 6)
    if c < a:
        return "halt"
    return (c - a + 3, 3 * a)


def check(n_rounds=25):
    """Compare the orbit with the machine (simple list simulator)."""
    t = {}
    for i, g in enumerate(M.split("_")):
        for y in (0, 1):
            s = g[3 * y:3 * y + 3]
            t[(i, y)] = None if s == "---" else (int(s[0]), 1 if s[1] == "R" else -1, ord(s[2]) - 65)
    tape, pos, st, step = {}, 0, 0, 0
    lo = hi = 0
    found = []
    while len(found) < n_rounds and step < 10 ** 9:
        tr = t[(st, tape.get(pos, 0))]
        if tr is None:
            raise SystemExit("machine halted?")
        tape[pos], d, st = tr
        pos += d
        step += 1
        lo, hi = min(lo, pos), max(hi, pos)
        if st == 0 and pos == lo:
            w = "".join(str(tape.get(p, 0)) for p in range(lo, hi + 1))
            parts = w.split("0")
            if len(parts) == 3 and parts[0] == "" and "" not in parts[1:]:
                found.append((step, len(parts[1]), len(parts[2])))
    return found


def main():
    args = [x for x in sys.argv[1:] if not x.startswith("--")]
    n = int(float(args[0])) if args else 10 ** 6
    if "--check" in sys.argv:
        rounds = check(16)
        a, c = 74, 30
        seq = [(a, c)]
        for _ in range(len(rounds)):
            a, c = mapc(a, c)
            seq.append((a, c))
        i = [r[1:] for r in rounds].index((74, 30))
        ok = [r[1:] for r in rounds][i:] == seq[:len(rounds) - i]
        print("machine round starts:", [r[1:] for r in rounds])
        print("agree with the map from (74, 30):", ok)
    a, c, t0 = 74, 30, time.time()
    closest = None
    for k in range(1, n + 1):
        r = mapc(a, c)
        if not isinstance(r, tuple):
            print(f"orbit step {k}: {r} at a={a}, c={c}")
            return
        a, c = r
        if k > 40:
            gap = abs(c - a).bit_length() - c.bit_length()
            if closest is None or gap < closest[1]:
                closest = (k, gap)
        if k % max(1, n // 10) == 0:
            print(f"{k} map steps: c has {c.bit_length()} bits ({time.time() - t0:.0f} s)", flush=True)
    print(f"{n} map steps: no halt, no small case; |c - a| never had fewer bits than c minus {-closest[1]} "
          f"(after step 40; at step {closest[0]})")


if __name__ == "__main__":
    main()
