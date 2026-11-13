"""The halving rule of 1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA, checked by plain simulation.

At the left end of the tape the run keeps coming back to   E> 0 1^x 0 0 1 0 ...   (state E, head on the blank cell
left of the leftmost block of x ones).  If x = 2k is even, the machine splits the block into two halves and comes
back to the same shape with x = k:

    E> 0 1^(2k) 0 0 1 0 R   ->   E> 0 1^k 0 0 1 0 1^k 0 R      (k >= 2; the tape grows by one cell to the left)

and for x = 2 (k = 1) it halts.  So a chain of halvings that starts from x = 2^j (j >= 1) ends in a halt; one that
starts from x = 2^j * odd with odd > 1 stops at the odd number and the head leaves on a long rightward sweep.

usage: python3 holdouts/1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA/py/halving.py [KMAX]
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "tools", "py"))
from bbtools.machine import Machine  # noqa: E402

M = "1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA"
E = 4


def next_e(k, tail, limit=10 ** 7):
    """From E> 0 1^(2k) 0 0 1 0 tail, run to the next E at the left end reading 0 (or a halt)."""
    pad = 10
    cells = [0] * pad + [0] + [1] * (2 * k) + [0, 0, 1, 0] + tail + [0] * pad
    m = Machine.parse(M)
    tape = dict(enumerate(cells))
    head, st = pad, E
    for n in range(1, limit + 1):
        t = m.table[st][tape.get(head, 0)]
        if t is None:
            return ("halt", n)
        w, d, st = t
        tape[head] = w
        head += d
        if st == E and tape.get(head, 0) == 0 and all(tape.get(i, 0) == 0 for i in range(head - 3, head)):
            return (n, head - pad, "".join(str(tape.get(i, 0)) for i in range(head, head + len(cells))))
    return None


def main():
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 80
    bad = 0
    for k in range(2, kmax + 1):
        for tail in ([1, 1, 0], [1, 1, 1, 1, 0, 1, 1, 0], [1, 1, 1, 0, 1, 1, 0]):
            r = next_e(k, tail)
            want = "0" + "1" * k + "0010" + "1" * k + "0" + "".join(map(str, tail))
            if not (r and r[0] != "halt" and r[1] == -1 and r[2].startswith(want)):
                bad += 1
                print("differs:", k, tail, r[:2] if r else r)
    print(f"halving held for k = 2..{kmax} with 3 tails each, {bad} exceptions")
    print("k = 1 (x = 2):", next_e(1, [1, 1, 0]))


if __name__ == "__main__":
    main()
