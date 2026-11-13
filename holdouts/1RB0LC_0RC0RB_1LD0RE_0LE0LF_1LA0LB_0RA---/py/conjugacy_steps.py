"""Check step by step (plain simulation, N steps) that each machine of the family, run from blank tape, is its
frame-A conjugate (frames.py) started in the given state, seen in a mirror when the frame is not A: same step,
mapped state, mirrored head position, same cells.  This is a test of frames.conjugate, which proves it from the
tables.

usage: python3 conjugacy_steps.py [N]
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import frames  # noqa: E402


def check(machine, N):
    fr, fa, st = frames.info(machine)
    mp = frames.frame_map(fr)
    sgn = 1 if fr == "A" else -1
    T1, T2 = frames.parse(fa), frames.parse(machine)
    t1, t2, p1, p2, q1, q2 = {}, {}, 0, 0, st, "A"
    for t in range(N):
        if mp[q1] != q2 or p1 != sgn * p2:
            return f"differ at {t}"
        y1, y2 = t1.get(p1, 0), t2.get(p2, 0)
        if y1 != y2:
            return f"cell differs at {t}"
        a, b = T1[(q1, y1)], T2[(q2, y2)]
        if a is None or b is None:
            return f"halt at {t}" if a is None and b is None else f"one halts at {t}"
        t1[p1], t2[p2] = a[0], b[0]
        p1 += 1 if a[1] == "R" else -1
        p2 += 1 if b[1] == "R" else -1
        q1, q2 = a[2], b[2]
    return f"same for {N} steps"


if __name__ == "__main__":
    N = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 6
    for m, fr, fa, st in frames.FAMILY:
        print(m, fr, fa, st, check(m, N))
