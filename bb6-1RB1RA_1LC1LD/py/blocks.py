"""Which pass starts of 1RB1RA_1LC1LD_1LD0LB_1RE0RF_---1RD_1RA1RB can lead to a halt: the search for a block-length
invariant (notes/LAB_NOTES.md, 31 October; lean/Blocks.lean for the part proved in Lean).

A pass start is a block list `b_1 ... b_k` (A on the blank cell right of the tape); it is *good* if every block is at
least 2 and the last block is neither 1 nor 4.  A last block 1 halts on this pass, 4 on the next one.

usage:
  python3 py/blocks.py run FILE             the pass starts in `tools/c/tmrun MACHINE STEPS at A R N` output: all
                                            good?  small blocks, and the recursive passes' last-block offsets
  python3 py/blocks.py exhaustive N K       every good list of at most K blocks of 2..N: which passes are not good
  python3 py/blocks.py random SEED COUNT    random good lists (blocks up to 200, last not 3 or 6): any pass not good?
  python3 py/blocks.py offsets N            for the recursive pass (..., x, 3j): last' - 2j against j, for x <= N
  python3 py/blocks.py chain N K SEED COUNT the open case A of lean/Chain.lean: a last block 3 after a block x >= 6,
                                            over all lists of at most K blocks (x up to 6 + N, the rest 2..N) and
                                            COUNT random ones: is the next pass start safe, and what are the offsets?
  python3 py/blocks.py caseb N X B K P      case B of lean/Chain.lean (lean/CaseB.lean): c = 0 against u = 2 on all
                                            lists of 1 to 3 blocks of 2..N; the safe starts `x b` (x even, x < X,
                                            b < B) that halt within K passes and how; and the first P passes of the run
"""
import itertools
import os
import random
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import macro  # noqa: E402

HALT = macro.HALT

# state -> ((write, move, next) on 0, on 1); None halts.  The machine of macro.M, written out for a fast loop.
TABLE = (((1, 1, 1), (1, 1, 0)), ((1, -1, 2), (1, -1, 3)), ((1, -1, 3), (0, -1, 1)),
         ((1, 1, 4), (0, 1, 5)), (None, (1, 1, 3)), ((1, 1, 0), (1, 1, 1)))
assert all(TABLE[s][y] == macro.MACHINE.table[s][y] for s in range(6) for y in (0, 1))


def good(bl):
    return bl != HALT and min(bl) >= 2 and bl[-1] not in (1, 4)


def one_pass(blocks, limit=10 ** 8):
    """From `blocks A>0` (blank around) to the next time A reads the blank cell right of the visited tape: the next
    pass start as a block list, or HALT."""
    cells = []
    for i, b in enumerate(blocks):
        cells += [1] * b + ([0] if i < len(blocks) - 1 else [])
    pad = 64
    t = [0] * pad + cells + [0] * pad
    lo = pad
    head = hi = pad + len(cells)
    s = 0
    for _ in range(limit):
        if head == 0 or head == len(t) - 1:
            grow = [0] * len(t)
            if head == 0:
                t = grow + t
                head, lo, hi = head + len(grow), lo + len(grow), hi + len(grow)
            else:
                t = t + grow
        tr = TABLE[s][t[head]]
        if tr is None:
            return HALT
        t[head], m, s = tr
        head += m
        lo = min(lo, head)
        hi = max(hi, head)
        if s == 0 and head == hi and t[head] == 0:
            return macro.blocks_of(t[lo:head])
    raise RuntimeError(f"no pass end in {limit} steps from {blocks}")


def run_file(path):
    seq = [macro.parse_tmrun(l)[1] for l in open(path) if l.strip().endswith("A>0")]
    bad = [bl for bl in seq if not good(bl)]
    small = Counter()
    for bl in seq:
        for i, v in enumerate(bl):
            if v < 10:
                small[("first" if i == 0 else "last" if i == len(bl) - 1 else "middle", v)] += 1
    offs, rec = Counter(), 0
    for a, b in zip(seq, seq[1:]):
        if a[-1] % 3 == 0:
            rec += 1
            offs[(b[-1] - 2 * (a[-1] // 3) == -1, a[-2] == 2 if len(a) > 1 else False)] += 1
            if b[-1] - 2 * (a[-1] // 3) < -1:
                raise AssertionError(f"recursive pass {a} -> {b}: last block below 2j - 1")
    lasts = sorted(set(bl[-1] for bl in seq))[:12]
    print(f"pass starts: {len(seq)}; not good: {len(bad)} {bad[:5]}")
    print(f"blocks below 10 (position, length): {dict(sorted(small.items()))}")
    print(f"smallest last blocks: {lasts}")
    print(f"recursive passes: {rec}; last' = 2j - 1 exactly when the block left of the last is 2: "
          f"{all(k[0] == k[1] for k in offs)} ({dict(offs)})")


def exhaustive(n, k):
    bad = []
    for size in range(1, k + 1):
        for bl in itertools.product(range(2, n + 1), repeat=size):
            if good(bl):
                r = one_pass(bl)
                if not good(r):
                    bad.append((bl, r))
    print(f"good lists of at most {k} blocks of 2..{n} whose next pass start is not good: {len(bad)}; their last "
          f"blocks: {dict(Counter(bl[-1] for bl, _ in bad))}")
    for bl, r in bad[:12]:
        print("  ", bl, "->", r)
    return bad


def random_check(seed, count):
    rnd = random.Random(seed)
    n, bad = 0, []
    while n < count:
        bl = tuple(rnd.choice([rnd.randint(2, 12), rnd.randint(2, 200)]) for _ in range(rnd.randint(1, 6)))
        if not good(bl) or bl[-1] in (3, 6):
            continue
        n += 1
        r = one_pass(bl)
        if not good(r):
            bad.append((bl, r))
    print(f"{n} random good lists with last block not 3 or 6: next pass start not good for {len(bad)} {bad[:5]}")
    return bad


def offsets(n, prefixes=((), (20,), (21,), (22,), (20, 21), (22, 22)), js=range(1, 25)):
    """For the recursive pass from (prefix, x, 3j): the set of last' - 2j over j.  Returns {(prefix, x): set}."""
    out = {}
    for pre in prefixes:
        for x in range(2, n + 1):
            out[(pre, x)] = {one_pass(pre + (x, 3 * j))[-1] - 2 * j for j in js}
    return out


def safe(bl):
    """`Safe` of lean/Chain.lean: good, at least two blocks, and a last block 3 only after a block of at least 6."""
    return good(bl) and len(bl) >= 2 and (bl[-1] != 3 or bl[-2] >= 6)


def chain(n, k, seed, count):
    """Case A of lean/Chain.lean: from `..., x, 3` with `x >= 6`, the next pass start, and the offset `c` and supply
    words `u` of `pre`.  Returns the lists whose next pass start is not safe, and the (c, u) seen."""
    rnd = random.Random(seed)
    lists = [(x,) + t for size in range(k) for t in itertools.product(range(2, n + 1), repeat=size)
             for x in range(6, n + 7)]
    lists += [tuple([rnd.randint(6, 300)] + [rnd.choice([rnd.randint(2, 12), rnd.randint(2, 300)])
                                            for _ in range(rnd.randint(0, 6))]) for _ in range(count)]
    bad, cu = [], Counter()
    for ls in lists:
        r = next_full_of(ls, 3)
        if not (r != HALT and r is not None and safe(r)):
            bad.append((ls, r))
        c, u = macro.offset(list(ls))
        cu[(min(c, 6), u)] += 1
    print(f"last block 3 after a block of at least 6: {len(lists)} lists, next pass start not safe for {len(bad)} "
          f"{bad[:5]}; (c, u) with c capped at 6: {dict(sorted(cu.items()))}")
    return bad, cu


def is_case_b(bl):
    """Case B of lean/Chain.lean: last block 6 after a block other than 2, recursive offset 0 (halts two passes on)."""
    return len(bl) >= 2 and bl[-1] == 6 and bl[-2] != 2 and macro.offset(list(reversed(bl[:-1])))[0] == 0


def path_of(bl, k):
    """The pass starts from `bl` for at most k passes; ends with HALT if the machine halts."""
    out = [bl]
    for _ in range(k):
        bl = macro.next_full(bl)
        out.append(bl)
        if bl == HALT or bl is None:
            break
    return out


def caseb(n, xmax, bmax, k, passes):
    """Case B (lean/CaseB.lean).  Returns a dict of the counts printed."""
    out = {}
    # 1. the offset c is 0 exactly when pre takes two supply words (block left of the last not 2)
    cu = Counter()
    for size in range(1, 4):
        for ls in itertools.product(range(2, n + 1), repeat=size):
            if ls[0] != 2:
                c, u = macro.offset(list(ls))
                cu[(c == 0, u == 2)] += 1
    out["c0_iff_u2"] = cu[(True, False)] == 0 and cu[(False, True)] == 0
    print(f"lists of 1 to 3 blocks of 2..{n}, nearest block not 2: c = 0 exactly when u = 2: {out['c0_iff_u2']} "
          f"({dict(cu)})")
    # 2. safe two-block starts with an even left block that halt within k passes
    halts, via_b, lasts, shrink_ok = [], 0, Counter(), True
    for x in range(2, xmax, 2):
        for b in range(2, bmax):
            if not safe((x, b)):
                continue
            pth = path_of((x, b), k)
            for a, c in zip(pth, pth[1:]):
                if c not in (HALT, None) and a[-1] not in (3, 6) and safe(a):
                    shrink_ok &= 2 * (a[-1] - 1) <= 3 * (c[-1] - 1) + 6
                    shrink_ok &= c[-1] != 6 or a[-1] == 9 or (a[-1] == 2 and a[-2] == 3)
            if pth[-1] == HALT:
                halts.append(pth)
                via_b += any(is_case_b(q) for q in pth[:-1])
                lasts[b] += 1
    out.update(halts=len(halts), via_b=via_b, lasts=dict(sorted(lasts.items())), shrink_ok=shrink_ok)
    print(f"safe starts x b, x even below {xmax}, b below {bmax}, halting within {k} passes: {len(halts)}, all by "
          f"case B: {via_b == len(halts)}; their last blocks: {out['lasts']}")
    print(f"safe_pass_shrink on every pass of these paths (2n <= 3n' + 6, a 6 only from 9 or 3 2): {shrink_ok}")
    for pth in sorted(halts, key=len)[-3:]:
        print("  ", " -> ".join(" ".join(map(str, q)) if q != HALT else q for q in pth))
    # 3. the run from 10 3 (blank_safe)
    seq = path_of((10, 3), passes)
    assert seq[-1] not in (HALT, None)
    even = all(q[0] % 2 == 0 for q in seq)
    zero, streak, best = 0, 0, 0
    for q in seq:
        if q[-1] % 3 == 0 and q[-2] != 2:
            if macro.offset(list(reversed(q[:-1])))[0] == 0:
                zero, streak = zero + 1, streak + 1
                best = max(best, streak)
                continue
        streak = 0
    rec = sum(q[-1] % 3 == 0 for q in seq)
    lows = {t: min(q[-1] for q in seq[t:]) for t in (0, 32, 156, 1000, 2000) if t < len(seq)}
    out.update(even=even, zero=zero, rec=rec, streak=best, lows=lows, case_b=sum(map(is_case_b, seq)))
    print(f"run, {len(seq) - 1} passes from 10 3: leftmost block always even: {even}; recursive passes {rec}, offset 0 "
          f"in {zero}, at most {best} in a row; case B reached: {out['case_b']}; smallest last block from pass t on: "
          f"{lows}")
    return out


def next_full_of(ls, b):
    """The next pass start from the blocks `ls` (nearest first) and a last block `b`, left to right."""
    return macro.next_full(tuple(reversed(ls)) + (b,))


def main(argv):
    if not argv:
        print(__doc__)
    elif argv[0] == "run":
        run_file(argv[1])
    elif argv[0] == "exhaustive":
        exhaustive(int(argv[1]), int(argv[2]))
    elif argv[0] == "random":
        random_check(int(argv[1]), int(argv[2]))
    elif argv[0] == "offsets":
        out = offsets(int(argv[1]))
        print("offsets independent of j:", all(len(v) == 1 for v in out.values()))
        print("smallest offset:", min(min(v) for v in out.values()),
              "; -1 exactly for x = 2:", all((min(v) == -1) == (x == 2) for (_, x), v in out.items()))
        for pre in sorted({p for p, _ in out}):
            print(" ", pre, [(x, *v) for (p, x), v in sorted(out.items()) if p == pre])
    elif argv[0] == "chain":
        chain(*map(int, argv[1:5]))
    elif argv[0] == "caseb":
        caseb(*map(int, argv[1:6]))
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
