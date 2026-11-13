"""Run random block lists (from `0^inf A> 0 (10)^b1 1 ... 1 0^inf`, frame A) and tally what the cells around the
head look like at each entry into F; a 1 under F is a halt.  Heuristic evidence for how fragile the family is.

usage: python3 random_lists.py FRAME_A_MACHINE SEED COUNT STEPS_EACH
"""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rle  # noqa: E402


def main(M, seed, n, budget):
    random.seed(seed)
    ctx, halts = {}, []
    for _ in range(n):
        L = [random.randint(0, 60) for _ in range(random.randint(1, 5))]
        s = rle.from_list(M, L)
        try:
            while s.steps < budget:
                if not s.try_cross():
                    q0 = s.q
                    s.step()
                    if s.q == 5 and q0 != 5:
                        l, r = rle.near(s, 12)
                        k = l[-8:] + "|" + r[:4]
                        ctx[k] = ctx.get(k, 0) + 1
        except rle.Halt:
            l, r = rle.near(s, 12)
            k = "HALT " + l[-8:] + "|" + r[:4]
            ctx[k] = ctx.get(k, 0) + 1
            halts.append((L, s.steps))
    for k, v in sorted(ctx.items(), key=lambda x: -x[1]):
        print(v, k)
    for L, t in halts:
        print("halts:", L, "after", t, "steps")


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]))
