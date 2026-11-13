"""cascade.py: check the halving-cascade map of 1RB0LE_0RC0RD_1LC0RB_0RE1RD_1LF1LE_0LA--- against the real run.

usage: python3 cascade.py EVENTS_FILE        (lines "STEPS TAPE" at the moments the head, in A, extends the tape
                                               to the left; see the README for how they are made)
       python3 cascade.py --run N             (simulate N steps here, in Python, and check them; slow)

At those moments the tape is  0^inf A> 0 0 1^n1 0 0 1^n2 0 0 ... 0 0 1^nk 0^inf  (blocks of 1s, gaps of two 0s).
The conjectured map from one moment to the next:
    v = n1, i = 1
    repeat:  n_i = floor(v/2);  c = v - n_i
             if v is odd (or i = 1 and n1 = 1, the merge):  n_(i+1) += c + 2,  n_(i+2) += 1  and stop
             else v = n_(i+1) + c, i += 1
(a block that is reached past the end is a new block 0), and a first block 1 merges: (1, x, y, ...) -> (x+3, y+1, ...).
The machine halts exactly when the map would make a block 0: past the end the carry c is halved again and again, and
a carry that is a power of 2 runs down to a block 0 (`random_check` compares the machine with this on random lists).
"""
import re
import sys


def step(ns):
    ns = list(ns)
    if ns[0] == 1:
        out = [ns[1] + 3] + ns[2:]
        if len(out) > 1:
            out[1] += 1
        else:
            out.append(1)
        return out
    v, i = ns[0], 0
    while True:
        h, c = v // 2, v - v // 2
        ns[i] = h
        while len(ns) < i + 3:
            ns.append(0)
        if v % 2:
            ns[i + 1] += c + 2
            ns[i + 2] += 1
            break
        v = ns[i + 1] + c
        i += 1
    return ns


def blocks(cells):
    s = cells.strip("0")
    if re.search("000", s):
        return None
    return [len(b) for b in s.split("00")]


def check(seq):
    bad = 0
    for (t0, a), (t1, b) in zip(seq, seq[1:]):
        if a is None or b is None or step(a) != b:
            bad += 1
            if bad <= 10:
                print("differs at", t0, a[:6] if a else a, "->", b[:6] if b else b, "predicted", step(a)[:6] if a else None)
    print(f"{len(seq) - 1} transitions, {bad} differ")


if __name__ == "__main__":
    seq = []
    for line in open(sys.argv[1]):
        t, cells = line.split()
        seq.append((int(t), blocks(cells)))
    check(seq)


def tm_step_list(ns, max_steps=10**7):
    """Run the machine from 0^inf A> 0 0 1^n1 0 0 ... 1^nk 0^inf until the head, in A, is left of every cell visited
    so far; return the block list there (or 'HALT' / None)."""
    T = {}
    m = "1RB0LE_0RC0RD_1LC0RB_0RE1RD_1LF1LE_0LA---".split("_")
    for s, g in enumerate(m):
        for r in (0, 1):
            x = g[3 * r:3 * r + 3]
            T[(s, r)] = None if x[0] == "-" else (int(x[0]), 1 if x[1] == "R" else -1, ord(x[2]) - 65)
    cells = "00" + "00".join("1" * n for n in ns)
    tape = {i: int(c) for i, c in enumerate(cells)}
    pos, st, lo = 0, 0, 0
    for _ in range(max_steps):
        tr = T[(st, tape.get(pos, 0))]
        if tr is None:
            return "HALT"
        w, d, st = tr
        tape[pos] = w
        pos += d
        if pos < lo:
            lo = pos
            if st == 0:
                hi = max(k for k, v in tape.items() if v) if any(tape.values()) else pos
                s = "".join(str(tape.get(k, 0)) for k in range(pos, hi + 1))
                return blocks(s) if s.startswith("00") else None
    return None


def random_check(trials=3000, seed=1):
    import random
    rnd = random.Random(seed)
    bad = 0
    for _ in range(trials):
        k = rnd.randint(1, 6)
        ns = [rnd.choice([1, 2, 3, 4, 5, 6, 7, 8, rnd.randint(1, 60)]) for _ in range(k)]
        if ns == [1]:
            continue
        got = tm_step_list(ns)
        want = step(ns)
        if 0 in want:
            want = "HALT"
        if got != want:
            bad += 1
            if bad <= 10:
                print("differs:", ns, "machine", got, "map", step(ns))
    print(f"{trials} random lists, {bad} differ")
