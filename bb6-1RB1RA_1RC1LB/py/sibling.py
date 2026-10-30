"""Compare 1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB with the sibling bbchallenge merged into an equivalence class.

usage:
  python3 sibling.py events STEPS     the tape at every time A is at the right end, for both machines, up to STEPS
  python3 sibling.py halts            halting from each macro configuration X(ls, n, cs) of a small family

The sibling 1RB1RA_1RC1LB_1LD0RA_1RA0LE_---0LF_0RD0LB shares states A, B, C with this machine and differs in D, E, F
(the states of the left-end and halting paths).  The holdout ledger lists it as "merged into another equivalence class
in April 2026" (mxdys, -d) without naming the class.  This script checks the claim that it is this machine:

  events  the tapes at each time A stands on the right end agree, in the same order (the step counts differ by a few
          steps per event);
  halts   from X(ls, n, cs) = 0^inf 1^{l_r} 0 ... 0 1^{l_1} 0 A> 1^n 000 1^{c_1} 00 ... 00 1^{c_s} 0^inf (the macro
          configurations of lean/Macro.lean), both machines halt within 20,000 steps or neither does.

Both checks are evidence, not a proof of equivalence.  Plain Python, no dependencies.
"""
import itertools
import sys

M = "1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB"
SIB = "1RB1RA_1RC1LB_1LD0RA_1RA0LE_---0LF_0RD0LB"


def parse(code):
    table = {}
    for q, blk in enumerate(code.split("_")):
        for r in range(2):
            t = blk[3 * r:3 * r + 3]
            table[q, r] = None if t[2] in "-Z" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
    return table


def run(code, tape, head, steps, on_step=None):
    """Run from `tape` (a dict) with the head at `head` in state A.  Returns the step count of the halt, or None."""
    table, q = parse(code), 0
    for k in range(1, steps + 1):
        t = table[q, tape.get(head, 0)]
        if t is None:
            return k
        tape[head] = t[0]
        head += t[1]
        q = t[2]
        if on_step:
            on_step(k, tape, head, q)
    return None


def events(code, steps):
    """The tape (as a string from the leftmost to the rightmost visited cell) at each time A is at the right end."""
    out, ext = [], [0, 0]

    def watch(k, tape, head, q):
        ext[0], ext[1] = min(ext[0], head), max(ext[1], head)
        if q == 0 and head == ext[1]:
            out.append("".join(str(tape.get(i, 0)) for i in range(ext[0], ext[1])))
    run(code, {}, 0, steps, watch)
    return out


def x_tape(ls, n, cs):
    cells = []
    for l in reversed(ls):
        cells += [1] * l + [0]
    left = len(cells)
    cells += [1] * n + [0, 0, 0]
    for i, c in enumerate(cs):
        cells += [1] * c + ([0, 0] if i < len(cs) - 1 else [])
    return {i - left: v for i, v in enumerate(cells)}


def main(argv):
    if argv[:1] == ["events"]:
        steps = int(argv[1]) if len(argv) > 1 else 10 ** 6
        a, b = events(M, steps), events(SIB, steps)
        k = min(len(a), len(b))
        bad = [i for i in range(k) if a[i] != b[i]]
        print(f"{k} events compared, {len(bad)} differ" + (f" (first at {bad[0]})" if bad else ""))
        return 1 if bad else 0
    if argv[:1] == ["halts"]:
        total = halting = differ = 0
        for r in range(4):
            for ls in itertools.product(range(1, 6), repeat=r):
                for n in range(8):
                    for cs in ([], [1], [3], [2, 5]):
                        h1 = run(M, x_tape(list(ls), n, cs), 0, 20000) is not None
                        h2 = run(SIB, x_tape(list(ls), n, cs), 0, 20000) is not None
                        total, halting, differ = total + 1, halting + h1, differ + (h1 != h2)
                        if h1 != h2:
                            print("differ:", ls, n, cs, h1, h2)
        print(f"{total} configurations, {halting} halt for this machine, {differ} disagree")
        return 1 if differ else 0
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
