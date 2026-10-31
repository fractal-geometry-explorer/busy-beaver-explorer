"""The pass structure of 1RB1RA_1LC1LD_1LD0LB_1RE0RF_---1RD_1RA1RB from blank tape.

The run keeps returning to A on the blank cell right of the tape, `1^{b_1} 0 1^{b_2} 0 ... 0 1^{b_k} A> 0^inf` (blocks
of ones separated by single 0s).  `next_pass` is one pass on the block list, as `lean/Macro.lean` (`next`,
`next_sound`) proves it, when the last block is not a multiple of 3; that case is recursive (the converter carries on
into the next block) and `next_pass` gives None for it.  `next_full` covers every pass: it is the `pass` of
`lean/Recur.lean` (`pass_sound`), the block machine `astep` transcribed line by line.

usage:
  python3 py/macro.py passes STEPS [K]     the pass starts of the run from blank tape (block lists), at most K lines
  python3 py/macro.py check STEPS          compare next_pass with the run: every non-recursive pass, and a census
  python3 py/macro.py check-file FILE      the same for `tools/c/tmrun MACHINE STEPS at A R N` output (grep 'A>0$')
  python3 py/macro.py check-full FILE      compare next_full (every pass, the recursive ones too) with such a file
"""
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools", "py"))

from bbtools.machine import Machine, Run  # noqa: E402

M = "1RB1RA_1LC1LD_1LD0LB_1RE0RF_---1RD_1RA1RB"
MACHINE = Machine.parse(M)
A = 0
HALT = "halt"


def next_pass(blocks):
    """The next pass start, as a tuple of blocks (left to right); HALT if the machine halts on this pass (last block
    1); None if the last block is a multiple of 3 (not covered).  Missing blocks at the left end count as 0.  The
    same function as `next` in lean/Macro.lean, written with b = n + 1 the last block."""
    *rest, b = blocks
    x = rest[-1] if rest else 0
    d = rest[-2] if len(rest) >= 2 else 0
    if b == 1:
        return HALT
    if b % 3 == 0:
        return None
    if b % 3 == 1:                      # n = b - 1 = 3m: the block to the left gains 6 + 2*floor((m - 1)/2)
        m = (b - 1) // 3
        return tuple(rest[:-1]) + (x + 6 + 2 * ((m - 1) // 2), 2 * m - 1)
    m = (b - 2) // 3                    # b = 3m + 2: two blocks to the left are rebuilt
    return tuple(rest[:-2]) + (d + 2 + 2 * ((m + 1) // 2), x + 2 * m + 3)


def tw(a, j, k):
    """`tw` in lean/Recur.lean: the word lengths a, 2 (j times), the last of them k longer."""
    w = [a] + [2] * j
    w[-1] += k
    return w


def bstep(n, c, d, M, k, W):
    """`bstep` in lean/Recur.lean: the converter B at a block n with c, d to its left, before a word 0 1^k."""
    if n % 3 == 1:
        return ("B", 0, [c, d] + M, [0] + tw(1, n // 3, k) + W)
    if n == 2:
        return ("E", k + 1, [c + 3, d] + M, W)
    if n % 3 == 2:
        return ("E", 1, [c + 3, d] + M, tw(2, n // 3 - 1, k) + W)
    if k == 0:
        return ("C", 0, [c, d] + M, tw(1, n // 3, 0) + W)
    if n == 0:
        return ("C", 0, [c, d] + M, [k + 1] + W)
    if n == 3:
        return ("A", k + 1, [c + 2, d + 2] + M, W)
    return ("A", 1, [c + 2, d + 2] + M, tw(2, n // 3 - 2, k) + W)


def astep(q, h, L, W):
    """`astep` in lean/Recur.lean, line by line: the block machine on (state, ones at the head, blocks to the left
    nearest first, word lengths to the right).  Returns a configuration, ("pass", ls, n) for the pass configuration
    `K ls n`, HALT, or None where it is not covered."""
    L = (list(L) + [0, 0, 0, 0])[:max(4, len(L))]
    a, M = L[0], L[1:]
    k, W1 = (W[0], W[1:]) if W else (None, None)
    if q == "A" and h > 0:
        return ("A", 0, [a + h] + M, W)
    if q == "A" and h == 0:
        if k is None:
            return ("pass", M, a - 1) if a > 0 else None
        return ("B", 0, [1] + [0] * (k - 1) + L, W1) if k > 0 else None
    if q in "DE" and h == (0 if q == "D" else 1):
        if k is None:
            return HALT
        a2 = a + (2 if q == "D" else 3)
        if k == 1:
            return ("D", 0, [a2] + M, W1)
        if k == 2:
            return ("F", 0, [0, a2] + M, W1)
        return ("B", 0, [1] + [0] * (k - 3) + [a2] + M, W1) if k > 2 else None
    if q == "F" and h == 0:
        return ("pass", M, a) if k is None else ("A", 0, [a + k + 1] + M, W1)
    if q == "C" and h == 0 and k is not None:
        if a > 0 and k == 1 and len(W1) > 0:
            return ("C", 0, [0] + M, [1, W1[0] + a] + W1[1:])
        if a > 0:
            return ("B", 0, [1] + [0] * k + [a - 1] + M, W1)
        d, M2 = M[0], M[1:]
        if k == 1:
            return ("F", 0, [0, d + 2] + M2, W1)
        return ("B", 0, [1] + [0] * (k - 2) + [d + 2] + M2, W1) if k > 1 else None
    if q == "B" and h == 0:
        if k is None:
            return ("pass", [L[3] + 2] + L[4:], L[2] + 1) if L[:2] == [1, 0] else None
        return bstep(L[0], L[1], L[2], L[3:], k, W1)
    return None


def pass_full(ls, n, fuel=10**9):
    """`pass` in lean/Recur.lean: from the pass configuration `K ls n` (blocks `ls` left of the last, nearest first,
    the last block n + 1) to the next one, ("pass", ls', n'), or HALT, or None (not covered, or out of fuel)."""
    blocks = tuple(reversed(ls)) + (n + 1,)
    p = next_pass(blocks)
    if p is not None and p != HALT:
        *rest, b = p
        return ("pass", list(reversed(rest)), b - 1)
    if n == 0:
        return HALT
    if n % 3 != 2:
        return None
    c = ("B", 0, list(ls[:1] or [0]) + list(ls[1:]), [0, 1] + tw(2, n // 3, 0))
    for _ in range(fuel):
        c = astep(*c)
        if c is None or c == HALT or c[0] == "pass":
            return c
    return None


def pre(ls, fuel=10**6):
    """`pre` in lean/Formula.lean: the recursive pass from `K ls (3j - 1)` before its final loop, the same for every j.
    The block machine runs from B before the words 0, 0 1, taking words 0 1 1 from an unbounded supply when it needs
    them (u counts them), until A has only words 0 1 1 ahead.  Returns (blocks to the left, two explicit, p words
    0 1 1 in front, u); the next pass start then has last block a + 2(p + j - u) = 2j + c, c = a + 2p - 2u."""
    q, h, L, W, u = "B", 0, list(ls[:1] or [0]) + list(ls[1:]), [0, 1], 0
    for _ in range(fuel):
        if q == "A" and h == 0 and all(w == 2 for w in W):
            return (L + [0, 0])[:max(2, len(L))], len(W), u
        if not W or (q == "C" and W == [1]):
            W, u = W + [2], u + 1
            continue
        r = astep(q, h, L, W)
        if r is None or r == HALT or r[0] == "pass":
            return None
        q, h, L, W = r
    return None


def offset(ls):
    """The offset c of `recur_sound` in lean/Formula.lean for the blocks `ls` (nearest first), and u."""
    L, p, u = pre(ls)
    return L[0] + 2 * p - 2 * u, u


def next_full(blocks):
    """The next pass start for every last block, as a tuple of blocks (left to right), from `pass_full`; HALT, or
    None if not covered.  Leading blocks of length 0 are dropped."""
    *rest, b = blocks
    r = pass_full(list(reversed(rest)), b - 1)
    if r is None or r == HALT:
        return r
    _, ls, n = r
    out = list(reversed(ls)) + [n + 1]
    while out and out[0] == 0:
        out.pop(0)
    return tuple(out)


def blocks_of(cells):
    s = "".join(map(str, cells)).strip("0")
    return tuple(len(p) for p in s.split("0"))


def pass_starts(steps):
    """Yield (step, blocks) each time A reads the blank cell right of the visited tape, from blank tape: the macro
    configuration.  Raises if a separator is not a single 0 (it never is in the runs checked)."""
    r = Run(MACHINE)
    while r.steps < steps and r.step():
        if r.state == A and r.head == r.tape.hi and r.tape.get(r.head) == 0:
            w = r.tape.word(r.tape.lo, r.head - 1)
            bl = blocks_of(w)
            if 0 in bl:
                raise ValueError(f"step {r.steps}: a separator of more than one 0: {r.config_str()}")
            yield r.steps, bl


def parse_tmrun(line):
    """(step, blocks) from a line `STEPS 1^a 0 1^b ... A>0` of tools/c/tmrun."""
    parts = line.split()
    bl = []
    for tok in parts[1:-1]:
        if tok.startswith("1"):
            bl.append(int(tok[2:]) if "^" in tok else 1)
        elif tok != "0":
            raise ValueError(f"a separator of more than one 0: {line.strip()}")
    return int(parts[0]), tuple(bl)


def check(seq):
    """Compare next_pass with consecutive pass starts. Returns (agree, recursive, census of last block mod 3,
    largest number of blocks)."""
    agree, rec, mod3, most = 0, 0, Counter(), 0
    prev = None
    for _, bl in seq:
        most = max(most, len(bl))
        if prev is not None:
            mod3[prev[-1] % 3] += 1
            p = next_pass(prev)
            if p is None:
                rec += 1
            elif p != bl:
                raise AssertionError(f"next_pass{prev} = {p}, the run gives {bl}")
            else:
                agree += 1
        prev = bl
    return agree, rec, mod3, most


def main(argv):
    if not argv:
        print(__doc__)
        return
    cmd = argv[0]
    if cmd == "passes":
        k = int(argv[2]) if len(argv) > 2 else 200
        for n, (t, bl) in enumerate(pass_starts(int(argv[1]))):
            if n >= k:
                break
            print(t, " ".join(map(str, bl)))
    elif cmd in ("check", "check-file"):
        seq = pass_starts(int(argv[1])) if cmd == "check" else (parse_tmrun(l) for l in open(argv[1]) if l.strip())
        agree, rec, mod3, most = check(seq)
        print(f"passes: {agree + rec}; next_pass agrees with the run on all {agree} it covers; {rec} recursive "
              f"(last block 0 mod 3); last block mod 3: {dict(sorted(mod3.items()))}; at most {most} blocks")
    elif cmd == "check-full":
        seq = [parse_tmrun(l)[1] for l in open(argv[1]) if l.strip()]
        rec = 0
        for a, b in zip(seq, seq[1:]):
            rec += a[-1] % 3 == 0
            if next_full(a) != b:
                raise AssertionError(f"next_full{a} = {next_full(a)}, the run gives {b}")
        print(f"passes: {len(seq) - 1}; next_full agrees with the run on all of them, {rec} recursive")
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
