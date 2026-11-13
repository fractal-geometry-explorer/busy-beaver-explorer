"""The block machine of 1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF, as in lean/Macro.lean, checked against the machine.

The tape is a row of blocks of 1s separated by single 0s, with one gap (two 0s side by side).  A macro configuration
is (b, ls, rs): the block b just left of the gap, the blocks ls further left and rs right of the gap, nearest first.
`mstep` and `mcost` are transcriptions of the Lean definitions.

usage: python3 macro.py check STEPS      run the machine STEPS steps; at every gap configuration the macro machine
                                          predicts (time and whole tape), compare
       python3 macro.py walls SWEEPS     the sweeps that reach the left end of the tape, and the block they carry
       python3 macro.py run N            N macro steps: the machine step reached (the number in lean/MacroRun.lean)
"""
import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "tools", "py"))
from bbtools.machine import Machine  # noqa: E402

MACHINE = "1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF"


def addH(k, ls):
    if not ls:
        return [] if k == 0 else [k]
    return [ls[0] + k] + ls[1:]


def rcost(m, c):
    return m * (2 * c + 2 * m + 7)


def run_cost(rs):
    return sum(x + 1 for x in rs)


def mstep(b, ls, rs):
    """One block at the gap: the next (b, ls, rs), or 'halt' / 'stuck'."""
    if b == 0:
        return "halt"
    x = addH(b // 2, ls)
    if b % 2 == 0:
        return (x[0], x[1:], [0] + addH(b // 2, rs))
    if not x:
        return "halt"
    if x[0] == 0:
        return "stuck"
    r = addH(3, addH(b // 2, rs))
    if not all(v >= 1 for v in r):
        return "stuck"
    full = list(reversed(r)) + x
    return (full[0], full[1:], [])


def mcost(b, rs):
    if b % 2 == 0:
        return rcost(b // 2 - 1, 2) + 8
    return rcost(b // 2, 1) + 8 + 1 + run_cost(addH(3, addH(b // 2, rs))) + 1


START = (3, [], [])   # the first gap, after 7 steps


def tape_of(s):
    """The cells of a gap configuration, left to right, and the head's index."""
    b, ls, rs = s
    cells = []
    for x in reversed(ls):
        cells += [1] * x + [0]
    cells += [1] * b + [0]
    head = len(cells)
    cells += [0]
    for x in rs:
        cells += [1] * x + [0]
    return cells, head


def check(steps):
    m = Machine.parse(MACHINE)
    tape, pos, st = {}, 0, 0
    s, due = START, 7
    t, n = 0, 0
    while t < steps:
        if t == due:
            cells, head = tape_of(s)
            lo = pos - head
            got = [tape.get(lo + i, 0) for i in range(len(cells))]
            outside = [p for p, v in tape.items() if v and not lo <= p < lo + len(cells)]
            assert st == 1 and got == cells and not outside, (t, s)
            n += 1
            nxt = mstep(*s)
            assert not isinstance(nxt, str), nxt
            due += mcost(s[0], s[2])
            s = nxt
        w, d, st2 = m.table[st][tape.get(pos, 0)]
        tape[pos] = w
        pos += d
        st = st2
        t += 1
    print(f"{n} gap configurations in the first {steps} steps, all as predicted")


def walls(sweeps):
    s, t, k = START, 7, 0
    while k < sweeps:
        b, ls, rs = s
        if not ls:
            print(f"sweep {k}: block {b} at the left end, machine step {t}")
        nxt = mstep(*s)
        if isinstance(nxt, str):
            print(nxt, "at sweep", k)
            return
        t += mcost(b, rs)
        if nxt[2] == []:
            k += 1
        s = nxt


def run(n):
    s, t, k = START, 7, 0
    for _ in range(n):
        nxt = mstep(*s)
        if isinstance(nxt, str):
            print(nxt)
            return
        t += mcost(s[0], s[2])
        if nxt[2] == []:
            k += 1
        s = nxt
    print(f"{n} macro steps, {k} sweeps, machine step {t}")


if __name__ == "__main__":
    cmd, n = sys.argv[1], int(float(sys.argv[2]))
    {"check": check, "walls": walls, "run": run}[cmd](n)
