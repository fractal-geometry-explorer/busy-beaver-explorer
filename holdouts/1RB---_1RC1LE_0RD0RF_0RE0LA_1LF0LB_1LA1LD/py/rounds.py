"""The first rounds of 1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD's sample map, exactly (see lean/Early.lean).

`jrun ROUNDS` prints the numbers `lean/Early.lean` checks: the jumps (a whole B phase is one jump), the map steps,
the R steps and the point reached.  `chains ROUNDS` lists every chain of C steps with s = 0 in those rounds: where it
starts (x, m), how many C steps it makes (j), the remainder y it ends with and the size h = (M+5)/2 of the next
step.  The chain halts the machine iff y = 0 (lean/Chain.lean, `chain`); the column 1/h is its chance under the
uniform-remainder heuristic of py/heuristic.py, summed in the last column.

usage (from the repository root): python3 holdouts/1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD/py/rounds.py jrun 20
       python3 holdouts/1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD/py/rounds.py chains 20
"""
import sys


def mstep(x, m, s):
    """The map of lean/MapThm.lean; None is H."""
    if m % 2 == 0:
        return (x - 1, m + 4, 1 - s) if x >= 1 else ((m + 6) // 2, 3 if s else 1, 0)
    if x == 0:
        return None
    if x >= (m + 5) // 2:
        return (x - (m + 5) // 2, 2 * m + 7 - s, s)
    if x + 1 == (m + 5) // 2 and s == 0:
        return (2 * x + 3, 1, 0)
    return (2 * x + 1, m + 4 - 2 * x, 1 - s)


def jrun(rounds):
    """Jumps as in lean/Early.lean until `rounds` R steps are made: (jumps, map steps, R steps, point)."""
    p, c, r, n = (7, 1, 0), 0, 0, 0
    while r < rounds:
        x, m, s = p
        if m % 2 == 0 and x >= 1:
            p, c = (0, m + 4 * x, s ^ (x & 1)), c + x
        else:
            if m % 2 == 0:
                r += 1
            p, c = mstep(x, m, s), c + 1
            if p is None:
                return n + 1, c, r, None
        n += 1
    return n, c, r, p


def chains(rounds):
    p, r, acc = (7, 1, 0), 0, 0.0
    rows = []
    prev_c0 = False
    while r < rounds:
        x, m, s = p
        c0 = m % 2 == 1 and s == 0 and x >= (m + 5) // 2
        if c0 and not prev_c0:
            x0, m0, j, q = x, m, 0, p
            while q[1] % 2 == 1 and q[2] == 0 and q[0] >= (q[1] + 5) // 2:
                q, j = mstep(*q), j + 1
            h = (q[1] + 5) // 2
            acc += 1 / h
            rows.append((r, x0, m0, j, q[0], h, acc))
        prev_c0 = c0
        if m % 2 == 0 and x >= 1:
            p = (0, m + 4 * x, s ^ (x & 1))
            prev_c0 = False
            continue
        if m % 2 == 0:
            r += 1
        p = mstep(x, m, s)
        if p is None:
            print("H in round", r)
            break
    print("round  start x  start m  j  remainder y  of h  1/h sum")
    for row in rows:
        print("%5d %8d %8d %2d %12d %5d  %.6f" % row)


if __name__ == "__main__":
    {"jrun": lambda R: print(*jrun(R)), "chains": chains}[sys.argv[1]](int(sys.argv[2]))
