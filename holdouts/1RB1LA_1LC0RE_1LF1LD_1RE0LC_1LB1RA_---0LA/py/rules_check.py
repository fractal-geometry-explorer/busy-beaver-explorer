"""Check the phase rules of 1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA by direct simulation from configurations.

S_t(x, c) is the head in state A on the first cell of `1^x (01)^2 1^6 (01)^c 1^t 0 1^2` (blank tape around), t = 3
or 6.  A "phase start" is the next time the head comes to the left end in state A with the tape of the form
`1^x' (01)^2 1^b (01)^c' T` (b = 3 or 6).

usage: python3 rules_check.py step XMAX          S_t(x, c) -> S_t(floor(3x/2)+7, c-2) for c = 4, 5, both t, x < XMAX
       python3 rules_check.py reset C T XMAX     the reset from S_T(x, C), C = 1 or 2, T = 3 or 6, for x < XMAX
"""
import re
import sys

M = "1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA"
TABLE = []
for s in M.split("_"):
    row = []
    for r in range(2):
        x = s[3 * r:3 * r + 3]
        row.append(None if x[0] == "-" else (int(x[0]), 1 if x[1] == "R" else -1, ord(x[2]) - 65))
    TABLE.append(row)
EV = re.compile(r"^1\^(\d+) \(01\)\^2 1\^(\d+) \(01\)\^(\d+) (.*)$")


def build(spec):
    cells = []
    for tk in spec.split():
        m = re.match(r"\((\d+)\)\^(\d+)", tk)
        if m:
            cells += [int(c) for c in m.group(1)] * int(m.group(2))
            continue
        b, _, n = tk.partition("^")
        cells += [int(b)] * (int(n) if n else 1)
    return cells


def words(tape, lo, hi):
    s = "".join(str(tape.get(i, 0)) for i in range(lo, hi + 1))
    out, i = [], 0
    while i < len(s):
        j = i
        if s[i] == "1":
            while j < len(s) and s[j] == "1":
                j += 1
            out.append(f"1^{j - i}")
            i = j
            continue
        k = 0
        while s[i + 2 * k:i + 2 * k + 2] == "01":
            k += 1
        if k >= 2:
            out.append(f"(01)^{k}")
            i += 2 * k
            continue
        out.append("0")
        i += 1
    return " ".join(out)


def events(spec, maxsteps):
    """Each arrival of the head at the left end of the tape, moving left: (steps, state, tape words)."""
    cells = build(spec)
    tape = dict(enumerate(cells))
    pos, st, lo, hi, n, was = 0, 0, 0, len(cells) - 1, 0, True
    while n < maxsteps:
        t = TABLE[st][tape.get(pos, 0)]
        if t is None:
            yield n, None, "HALT"
            return
        tape[pos] = t[0]
        pos += t[1]
        st = t[2]
        n += 1
        lo, hi = min(lo, pos), max(hi, pos)
        at = pos == lo and t[1] == -1
        if at and not was:
            yield n, st, words(tape, lo, hi)
        was = at


def next_start(spec, cmin, maxsteps=10 ** 8):
    """The next phase start (x', b, c', tail) with c' >= cmin and the head in A, or ("HALT", steps, last words)."""
    last = None
    for n, st, s in events(spec, maxsteps):
        if s == "HALT":
            return ("HALT", n, last)
        last = f"{'ABCDEF'[st]}< {s}"
        m = EV.match(s)
        if m and st == 0 and n > 10 and int(m.group(3)) >= cmin and int(m.group(2)) in (3, 6):
            return int(m.group(1)), int(m.group(2)), int(m.group(3)), m.group(4)
    return None


def main(argv):
    if argv[0] == "step":
        bad = total = 0
        for t in (3, 6):
            for c in (4, 5):
                for x in range(1, int(argv[1])):
                    got = next_start(f"1^{x} (01)^2 1^6 (01)^{c} 1^{t} 0 1^2", 0)
                    want = (3 * x // 2 + 7, 6, c - 2, f"1^{t} 0 1^2")
                    total += 1
                    if got != want:
                        bad += 1
                        print("mismatch", t, c, x, got, want)
        print(f"{total} steps checked, {bad} mismatches")
    else:
        c, t, xmax = int(argv[1]), int(argv[2]), int(argv[3])
        for x in range(1, xmax):
            body = f"(01)^{c} " if c > 1 else "0 1 "
            print(x, next_start(f"1^{x} (01)^2 1^6 {body}1^{t} 0 1^2", c + 3), flush=True)


if __name__ == "__main__":
    main(sys.argv[1:])
