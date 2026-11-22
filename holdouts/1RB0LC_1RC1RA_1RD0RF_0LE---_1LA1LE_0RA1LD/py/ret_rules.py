"""Find the rules of the return after a 00 pulse of 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD and write lean/Return.lean.

After the right sweep every word to the left of the head is an image, 11 (word 01) or 100 (word 011). Random tapes
"images, 001, random words, a run of 1s, words" are run from state A at the 00; each time the head, moving left,
enters the last cell of an image, its state S and the six cells to the right of the image (the carry c) are recorded.
From these entries the script closes the set of modes (S, c): it runs each image from each mode on 12 random tapes
around it and keeps the result if it is always the same and the head never goes beyond the carry; the new mode is the
state on reaching the next image and the first six cells of the result. Each kept result becomes one theorem, proved
by rfl in Lean (for every tape around), so the random tapes only choose which rules to state.

usage: python3 py/ret_rules.py        # rewrites lean/Return.lean, prints the rules
"""
import os
import random

HERE = os.path.dirname(os.path.abspath(__file__))
M = "1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD"
T = {}
for i, s in enumerate(M.split("_")):
    for b in (0, 1):
        x = s[3 * b:3 * b + 3]
        T[(i, b)] = None if x[0] == "-" else (int(x[0]), 1 if x[1] == "R" else -1, ord(x[2]) - 65)
IMG = {"0": "11", "1": "100"}
W = 6
S6 = "ABCDEF"


def entries(n=300):
    found = set()
    for sd in range(n):
        random.seed(sd)
        lw = [random.choice("01") for _ in range(16)]
        lc = "".join(IMG[b] for b in lw)
        starts, pos = [], 0
        for b in lw:
            starts.append(pos)
            pos += len(IMG[b])
        starts.append(pos)
        right = ("001" + "".join(random.choice(["01", "011"]) for _ in range(random.randint(0, 8))) + "0" +
                 "1" * random.randint(3, 9) + "0" + "".join(random.choice(["01", "011"]) for _ in range(4)) + "0" * 30)
        x = lc + right
        tape = {i: int(c) for i, c in enumerate(x)}
        p, st, last = len(lc), 0, None
        for _ in range(20000):
            tr = T[(st, tape.get(p, 0))]
            if tr is None:
                break
            w, d, st = tr
            tape[p] = w
            p += d
            if p < 0:
                break
            for j in range(15, -1, -1):
                if p == starts[j + 1] - 1 and d < 0 and (last is None or j < last):
                    a = starts[j + 1]
                    found.add((S6[st], "".join(str(tape.get(i, 0)) for i in range(a, a + W))))
                    last = j
                    break
    return found


def cross(left, u, s, carry, right):
    x = left + IMG[u] + carry + right
    a, b = len(left), len(left) + len(IMG[u])
    tape = {i: int(c) for i, c in enumerate(x)}
    p, st, mx = b - 1, s, b - 1
    for k in range(400):
        tr = T[(st, tape[p])]
        if tr is None:
            return "halt"
        w, d, st = tr
        tape[p] = w
        p += d
        mx = max(mx, p)
        if mx >= b + len(carry):
            return "beyond"
        if p == a - 1:
            return (S6[st], "".join(str(tape[i]) for i in range(a, b + len(carry))), k + 1)
    return "loop"


def rule(s, u, c):
    res = set()
    for _ in range(12):
        left = "".join(random.choice(["11", "100"]) for _ in range(5))
        right = "".join(random.choice("01") for _ in range(8))
        res.add(cross(left, u, S6.index(s), c, right))
    return res.pop() if len(res) == 1 else None


def main():
    random.seed(12345)
    todo, seen = sorted(entries()), {}
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen[m] = {}
        for u in "01":
            r = rule(m[0], u, m[1])
            seen[m][u] = r
            if isinstance(r, tuple):
                todo.append((r[0], r[1][:W]))
    lb = lambda s: "[" + ", ".join("true" if c == "1" else "false" for c in s) + "]"
    body = []
    for (s, c) in sorted(seen):
        for u, r in sorted(seen[(s, c)].items()):
            word = "w01" if u == "0" else "w011"
            if not isinstance(r, tuple):
                print(f"{s} {c} {word}: {r}")
                continue
            s2, out, k = r
            im = IMG[u]
            print(f"{s} {im}|{c} -> {out} {s2} ({k} steps)")
            body.append(f"theorem ret_{s}_{c}_{word} (L R : Tape) :\n"
                        f"    steps {k} ⟨app {lb(im[:-1][::-1])} L, app {lb(im[-1] + c)} R, .{s}⟩ =\n"
                        f"      some ⟨tail L, cons (L 0) (app {lb(out)} R), .{s2}⟩ := rfl\n")
    path = os.path.join(HERE, "..", "lean", "Return.lean")
    head = open(path).read().split("open TM\n")[0] + "open TM\n\n"
    open(path, "w").write(head + "\n".join(body) + "\nend H126068\n")


if __name__ == "__main__":
    main()
