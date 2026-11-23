"""Toward an invariant of the block lists of 1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---: which lists halt within one
tick, and which local conditions the run keeps.

usage: python3 py/invariant.py B.txt     B.txt from `c/blocks STEPS` (the block list at every right-end turn)

1. Every list of at most MAXM blocks of lengths 0..MAXB (any separators) is run for one tick on a plain simulator,
   from its right-end turn `… A> 1 1`, with blank tape to the left: does it halt before the next right-end turn?
2. The local condition C: every block 1 has a separator 1 before it, and every block 0 stands between two
   separators 1 and is followed by an odd block of length ≥ 3.  The run keeps C at every right-end turn of B.txt
   (after the first list), and no list of part 1 that satisfies C halts in its tick.
3. C alone is not kept by a tick: the lists of part 1 that satisfy C and whose next list does not.

This is a computation, not a proof.  An invariant that rules out the halt needs more than C: the lists of the run
also keep the parity structure of the tick families, which C does not see.
"""
import itertools
import re
import sys

T = {'A': [(1, 1, 'B'), (0, -1, 'E')], 'B': [(0, 1, 'C'), (0, 1, 'A')], 'C': [(1, 1, 'D'), (1, 1, 'F')],
     'D': [(1, -1, 'A'), (0, -1, 'D')], 'E': [(1, -1, 'D'), (0, 1, 'F')], 'F': [(1, 1, 'B'), None]}
MAXM, MAXB = 5, 5


def name(blocks, seps):
    return str(blocks[0]) + "".join(s + str(n) for s, n in zip(seps, blocks[1:]))


def tick(blocks, seps, limit=400000):
    """the next list (blocks, seps), 'HALT', or 'long'"""
    bits = [1, 0] * blocks[0]
    for n, s in zip(blocks[1:], seps):
        bits += [1 if s == "|" else 0] + [1, 0] * n
    off = 3000
    tape = bytearray(2 * off + len(bits) + 3000)
    tape[off:off + len(bits)] = bytes(bits)
    h, s = off + len(bits), "A"
    tape[h] = tape[h + 1] = 1
    for t in range(limit):
        if t and s == "A" and tape[h] == 1 and tape[h + 1] == 1 and not any(tape[h + 2:h + 60]):
            b = tape[:h]
            st = b.index(1)
            out, sp, start = [], [], st
            for p in range(st, len(b) - 1):
                if b[p] == b[p + 1]:
                    sep = p if b[p] else p + 1
                    out.append((sep - start) // 2)
                    sp.append("|" if b[p] else ".")
                    start = sep + 1
            out.append((len(b) - start) // 2)
            return out, sp
        tr = T[s][tape[h]]
        if tr is None:
            return "HALT"
        w, d, s = tr
        tape[h] = w
        h += d
    return "long"


def cond(blocks, seps):
    for i, n in enumerate(blocks):
        before = seps[i - 1] if i else "^"
        after = seps[i] if i < len(seps) else "$"
        if n == 1 and before != "|":
            return False
        if n == 0 and not (before == "|" and after == "|" and blocks[i + 1] % 2 == 1 and blocks[i + 1] >= 3):
            return False
    return True


def main(path):
    lists = []
    for ln in open(path):
        lst = ln.split()[1]
        lists.append((list(map(int, re.findall(r"\d+", lst))), re.findall(r"[|.]", lst)))
    kept = sum(cond(*x) for x in lists[1:])
    print(f"the run: C holds at {kept} of the {len(lists) - 1} right-end turns after the first")
    total = halts = halts_c = with_c = leave = 0
    ex_halt, ex_leave = [], []
    for m in range(1, MAXM + 1):
        for blocks in itertools.product(range(MAXB + 1), repeat=m):
            if blocks[0] == 0:
                continue
            for seps in itertools.product("|.", repeat=m - 1):
                total += 1
                c = cond(blocks, seps)
                with_c += c
                r = tick(list(blocks), list(seps))
                if r == "HALT":
                    halts += 1
                    halts_c += c
                    if len(ex_halt) < 8:
                        ex_halt.append(name(blocks, seps))
                elif c and (r == "long" or not cond(*r)):
                    leave += 1
                    if len(ex_leave) < 8:
                        ex_leave.append(f"{name(blocks, seps)} -> {r if r == 'long' else name(*r)}")
    print(f"lists of at most {MAXM} blocks of length 0..{MAXB}: {total}; {halts} halt in their tick "
          f"(e.g. {', '.join(ex_halt)}); of the {with_c} with C, {halts_c} halt")
    print(f"C is not kept: {leave} lists with C give a next list without it (e.g. {'; '.join(ex_leave)})")


if __name__ == "__main__":
    main(sys.argv[1])
