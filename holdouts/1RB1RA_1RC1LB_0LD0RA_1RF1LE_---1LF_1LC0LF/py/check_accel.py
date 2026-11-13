"""Cross-check accel.py (run-length simulator with the Lean-proved M/Z moves) against plain simulation (../c/blk.c):
for random block lists, the next block configuration and its step count must agree (or both halt).

usage: python3 check_accel.py [COUNT [SEED]]
"""
import random, sys

from accel import Sim, C, push
from verify_rounds import build, round_


def next_block(bl, maxn=10 ** 11, chain=False):
    sim = Sim()
    sim.chain = chain
    for i, b in enumerate(bl):
        if i:
            push(sim.L, 0, 1)
        push(sim.L, 1, b)
    sim.s, sim.h = C, 0
    first = True
    while sim.n < maxn:
        if not first and sim.s == C and sim.h == 0 and not sim.R and sim.L and sim.L[-1][0] == 1:
            b = sim.blocks()
            if b is not None:
                return sim.n, b
        first = False
        if not sim.macro():
            sim.step()
            if sim.halted:
                return "halt", None
    return "max", None


def main(count, seed):
    build()
    random.seed(seed)
    k = 0
    while k < count:
        nb = random.randint(1, 4)
        bl = [random.randint(1, 12) for _ in range(nb)]
        # bias towards overflow rounds n = 2A+3 and odd/even rounds
        r = random.random()
        A = bl[-1]
        bl.append(2 * A + 3 if r < 0.5 else random.randint(2, 2 * A + 3))
        a = round_(bl, 10 ** 9)
        if a[0] == "max":
            continue
        b = next_block(bl, 10 ** 9)
        assert (a[0], a[1]) == (b[0], b[1]), (bl, a, b)
        k += 1
    print(f"ok: {k} rounds agree (seed {seed})")
    # the run from blank tape with and without runs of odd rounds: the block configurations of the first are among
    # those of the second, with the same step counts
    from accel import run
    sim1, a = run(10 ** 200)
    on = set(map(repr, a))
    sim0 = Sim(); sim0.chain = False
    seen = set()
    while sim0.n < 10 ** 200 and not sim0.halted:
        if sim0.s == C and sim0.h == 0 and not sim0.R and sim0.L and sim0.L[-1][0] == 1:
            b = sim0.blocks()
            if b is not None:
                seen.add(repr((sim0.n, b)))
        if not sim0.macro():
            sim0.step()
    assert on <= seen, sorted(on - seen)[:3]
    print(f"ok: {len(on)} block configurations of the accelerated run to 10^200 are among the {len(seen)} of the plain one")


if __name__ == "__main__":
    a = [int(x) for x in sys.argv[1:3]]
    main(a[0] if a else 300, a[1] if len(a) > 1 else 1)
