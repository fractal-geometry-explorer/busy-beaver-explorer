"""The macro step of 1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB as a map on lists of block lengths.

The same map as `next` in ../lean/Macro.lean, where it is proved to be what the machine does (`next_sound`), step
counts included.  A macro configuration is

    X(ls, n, cs) = 0^inf 1^{l_r} 0 ... 0 1^{l_1} 0 A> 1^n 0 0 0 1^{c_1} 0 0 ... 0 0 1^{c_s} 0^inf

with ls = [l_1, ..., l_r] nearest the head first.  The run from blank tape is at X([1], 2, []) after 15 steps.

usage: python3 macro.py [MACRO_STEPS]      print the run's macro configurations
"""
import sys


def bump(cs, q=1):
    """The first block gains q (a new block q if there is none)."""
    if q == 0:
        return list(cs)
    return [cs[0] + q] + list(cs[1:]) if cs else [q]


def sweep(ls, m, cs):
    """A sweeps right from `0 A> 1^m 0 0 [cs]`: each 00 becomes 0, the block gains 2, A takes one cell of the next
    block. Returns (ls, n, cs, steps) of the macro configuration at the right end."""
    t = 0
    ls = list(ls)
    for c in cs:
        assert c >= 1
        t += m + 3
        ls = [m + 2] + ls
        m = c - 1
    return ls, m, [], t


def next_step(ls, n, cs):
    """One macro step from X(ls, n, cs): ('go', ls, n, cs, steps) or ('halt', steps), where steps counts ordinary
    transitions (the halting transition is one more)."""
    q, e = divmod(n, 2)
    t = q * (2 * e + 2 * q + 9)                       # q transfers
    ls = [ls[0] + q] + list(ls[1:])
    cs = bump(cs, q)
    if e == 0:                                        # empty block: sweep right
        ls = bump(ls)
        if not cs:
            return ('go', ls, 2, [], t + 15)
        ls2, n2, cs2, t2 = sweep(ls, cs[0] + 2, cs[1:])
        return ('go', ls2, n2, cs2, t + 15 + t2)
    t += 6                                            # one cell left: carry to the left
    i = 0
    while i < len(ls) and ls[i] == 2:
        t += 5
        i += 1
    if i == len(ls):
        return ('halt', t + 6)
    k, rest = ls[i], ls[i + 1:]
    assert k >= 1
    if k >= 3:
        return ('go', bump(rest), k - 3, [1] * (i + 1) + bump(cs), t + k + 6)
    ls2, n2, cs2, t2 = sweep(bump(rest), 2, [1] * i + bump(cs))
    return ('go', ls2, n2, cs2, t + 15 + t2)


def run(macro_steps):
    """The macro run from blank tape: yields (macro step, machine steps, ls, n, cs), then ('halt', steps) if it halts."""
    ls, n, cs, t = [1], 2, [], 15
    yield 0, t, ls, n, cs
    for m in range(1, macro_steps + 1):
        r = next_step(ls, n, cs)
        if r[0] == 'halt':
            yield 'halt', t + r[1]
            return
        _, ls, n, cs, dt = r
        t += dt
        yield m, t, ls, n, cs


def tape(ls, n, cs):
    """The cells of X(ls, n, cs) from the first 1 to the last, and the head's index among them (blocks >= 1)."""
    left = []
    for l in reversed(ls):
        left += [1] * l + [0]
    right = [1] * n + [0, 0, 0]
    for j, c in enumerate(cs):
        right += [1] * c + ([0, 0] if j < len(cs) - 1 else [])
    cells = left + right
    while cells and cells[-1] == 0:
        cells.pop()
    return cells, len(left)


if __name__ == "__main__":
    for row in run(int(sys.argv[1]) if len(sys.argv) > 1 else 50):
        print(*row)
