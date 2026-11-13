"""The phase map of 1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---, found by fitting and checked against direct runs.

At the start of a phase the tape is  Q 0 1^m (01)^5 1 D>0  (Q a short prefix, possibly empty, then no 0).
Inside a phase the proved cycle (lean/Cycle.lean) turns 1^(x+3) (01)^y into 1^x (01)^(y+4) until fewer than three
1s are left; what happens next depends on Q and r = m mod 3, and gives the next phase  Q' 0 1^m' (01)^5 1 D>0.

`phase(Q, m)` runs the machine cell by cell from that configuration to the next phase start.  `fit(Q, r)` runs it
for m = 3k + r, k = 6..9, and fits m' = a k + b and the step count as a quadratic in k; every case found so far is
m' = 8k + b, a fixed Q', and steps = 12k^2 + Bk + C, exact on the four samples.  `run` iterates the fitted map.

The fitted map is not a proof: each case's linearity in k is checked on four values only.  It agrees with the direct
C run (tools/c/tmrun.c) on the first ten phases, to step 1.67e10 (see README).

usage: python3 phasemap.py [PHASES]        iterate the map from the first regular phase ('' with m = 38, step 576)
       python3 phasemap.py cases [N]       the case table of the first N prefixes reached (breadth first)
"""
import re
import sys

M = "1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---"
T = {}
for s, part in enumerate(M.split("_")):
    for r in (0, 1):
        t = part[3 * r:3 * r + 3]
        T[(s, r)] = None if t[2] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
PAT = re.compile(r"^(?:(.*)0)?(1+)((?:01){5})1$")
D = 3


def phase(Q, m, maxsteps=10 ** 8):
    """From Q 0 1^m (01)^5 1 D>0 to the next phase start: (Q', m', steps), or ('HALT', steps)."""
    s = (Q + "0" if Q else "") + "1" * m + "01" * 5 + "1"
    tape = {i: int(c) for i, c in enumerate(s)}
    head, st, lo, hi, steps = len(s), D, 0, len(s), 0
    while steps < maxsteps:
        tr = T[(st, tape.get(head, 0))]
        steps += 1
        if tr is None:
            return ("HALT", steps)
        w, d, st = tr
        tape[head] = w
        head += d
        lo = min(lo, head)
        if head > hi:
            hi = head
            if st == D:
                cells = "".join(str(tape.get(i, 0)) for i in range(lo, hi)).lstrip("0")
                mm = PAT.match(cells)
                if mm and len(mm.group(2)) >= 3:
                    return (mm.group(1) or "", len(mm.group(2)), steps)
    return ("TIMEOUT", steps)


table = {}


def fit(Q, r):
    if (Q, r) in table:
        return table[(Q, r)]
    ks = [6, 7, 8, 9]
    outs = [phase(Q, 3 * k + r) for k in ks]
    res = None
    if any(o[0] in ("HALT", "TIMEOUT") for o in outs) or len({o[0] for o in outs}) != 1:
        res = ("IRREGULAR", outs)
    else:
        a = outs[1][1] - outs[0][1]
        b = outs[0][1] - a * ks[0]
        s = [o[2] for o in outs]
        A2 = (s[2] - 2 * s[1] + s[0])           # 2A
        B = (s[1] - s[0]) - A2 * (2 * ks[0] + 1) // 2
        C = s[0] - A2 * ks[0] ** 2 // 2 - B * ks[0]
        ok = all(outs[i][1] == a * ks[i] + b for i in range(4)) and A2 % 2 == 0 and \
            all(A2 // 2 * k * k + B * k + C == s[i] for i, k in enumerate(ks))
        res = (outs[0][0], a, b, (A2 // 2, B, C)) if ok else ("IRREGULAR", outs)
    table[(Q, r)] = res
    return res


def short(w):
    """A compact form of a word: runs of 1 and of 01 counted."""
    out, i = [], 0
    while i < len(w):
        j = i
        while j + 2 <= len(w) and w[j:j + 2] == "01":
            j += 2
        if j > i:
            out.append("(01)^%d" % ((j - i) // 2) if j - i > 2 else "01")
            i = j
            continue
        j = i
        while j < len(w) and w[j] == w[i]:
            j += 1
        out.append(w[i] + ("^%d" % (j - i) if j - i > 1 else ""))
        i = j
    return " ".join(out) or "''"


def run(phases, Q="", m=38, start=576, out=print):
    total = start
    for i in range(phases):
        r, k = m % 3, m // 3
        if k < 6:
            Q2, m2, st = phase(Q, m)
        else:
            t = fit(Q, r)
            if t[0] == "IRREGULAR":
                out("phase %d: case %s r=%d is irregular: %s" % (i, short(Q), r, t[1]))
                return
            Q2, a, b, (A, B, C) = t
            m2, st = a * k + b, A * k * k + B * k + C
        out("%d start step %s  Q=%s  m=%s  r=%d" % (i, total if total < 10 ** 15 else "~10^%d" % (len(str(total)) - 1),
                                                 short(Q), m if m < 10 ** 15 else "~10^%d" % (len(str(m)) - 1), r))
        total += st
        Q, m = Q2, m2


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "cases":
        seen, todo, n = set(), [""], int(sys.argv[2]) if len(sys.argv) > 2 else 20
        while todo and len(seen) < n:
            Q = todo.pop(0)
            if Q in seen:
                continue
            seen.add(Q)
            for r in (0, 1, 2):
                t = fit(Q, r)
                if t[0] == "IRREGULAR":
                    print(short(Q), r, "IRREGULAR")
                else:
                    print("%-22s r=%d -> %-22s m' = 8k+%d   steps = %dk^2+%dk+%d" % (short(Q), r, short(t[0]), t[2], *t[3]))
                    todo.append(t[0])
    else:
        run(int(sys.argv[1]) if len(sys.argv) > 1 else 12)
