"""The super orbit by periodic tables, in Python: an independent version of c/superrun.c (see there for the method).

usage:
  python3 superrun.py MAX_SUPER_STEPS      the returns to the left end, as "S T d1 m": super step S (counted from 1)
                                           ends at machine step T, d1 = N / 2^(m-1)
  python3 superrun.py plan K PASSES        the plan of lean/CascadeRun.lean: tables for K levels, then PASSES passes;
                                           and the super step and machine step it ends at

The levels are the blocks counted from the right end (level 0 = p_m).  Each super step level 0 receives a wave
with h = 10; a level with block p receiving a wave h has d = p + h and either (d odd) becomes (d + 5)/2 and adds
(d - 1)/2 to the level above, or (d even) becomes d/2 and sends the wave d/2 on.  The bottom K levels never see
what happens above them, so once they repeat, what they send to level K is a periodic sequence: the table.
"""
import sys

ADD, WAVE = 0, 1


def g(d):
    """Machine steps for a level that receives a wave and has d = p + h (see c/superrun.c)."""
    c = d - 4
    j = c // 2
    return (d + 1) + j * (2 * c + 7) - 2 * j * j + 3 + j


class Halt(Exception):
    pass


def left_end(up, d1, T):
    """The wave passed the top level with d = d1: the left-end rule of waves.superstep, and its machine steps."""
    s, u = 0, d1
    while u % 2 == 0:
        s, u = s + 1, u // 2
    if u == 1:
        raise Halt(d1)
    del up[-1]
    if d1 % 2:
        T += 17
    else:
        e = d1
        while True:
            e //= 2
            if e == 3:
                T += 16
                break
            T += g(e)
            if e % 2:
                T += 17
                break
    up += [u << t for t in range(s - 1, -1, -1)] + [(u + 5) // 2, (u - 1) // 2]
    return T


def run(max_s, start=None, max_k=None, plan=None, last_passes=None):
    """Yield (S, T, d1, m) at each return to the left end, up to super step max_s (or ('halt', S, d1)).  With max_k,
    tabulate at most max_k levels; with a list plan, append (passes, L) for each table built: the plan that
    lean/CascadeRun.lean evaluates, which ends with (last_passes, 0) and the final ("end", S, T)."""
    tab, tail, K = [(1, WAVE, 10, 210)], (0, 0), 0
    if start:
        up, T = list(reversed(start)), 0
    else:
        up, T = [6, 1], 136
    S, seen, wraps = 0, {}, 0
    while True:
        for dt, typ, v, c in tab:
            S += dt
            T += c
            if typ == ADD:
                up[0] += v
                T += 17
            else:
                h, k = v, 0
                while True:
                    d = up[k] + h
                    T += g(d)
                    if k == len(up) - 1:
                        try:
                            T = left_end(up, d, T)
                        except Halt:
                            yield ("halt", S, d)
                            return
                        yield (S, T, d, K + len(up))
                        break
                    if d % 2:
                        up[k], up[k + 1] = (d + 5) // 2, up[k + 1] + (d - 1) // 2
                        T += 17
                        break
                    up[k] = h = d // 2
                    k += 1
            if S >= max_s:
                return
        S += tail[0]
        T += tail[1]
        wraps += 1
        if K == max_k and wraps == last_passes:
            plan.append((wraps, 0))
            yield ("end", S, T)
            return
        if len(up) < 3 or K == max_k:
            continue
        if up[0] in seen:
            new = periodic_table(tab, tail, up[0], wraps - seen[up[0]])
            if new:
                if plan is not None:
                    plan.append((wraps, wraps - seen[up[0]]))
                tab, tail = new
                K += 1
                up = up[1:]
                seen, wraps = {}, 0
                continue
        seen[up[0]] = wraps


def periodic_table(tab, tail, p0, L):
    """The table for level K + 1 from L passes of level K (block p0) over the table for K, or None if those passes do
    not bring level K back to p0."""
    p, new, adt, ac = p0, [], 0, 0
    for _ in range(L):
        for dt, typ, v, c in tab:
            adt += dt
            ac += c
            if typ == ADD:
                p += v
                ac += 17
                continue
            d = p + v
            ac += g(d)
            if d % 2:
                new.append((adt, ADD, (d - 1) // 2, ac))
                p = (d + 5) // 2
            else:
                new.append((adt, WAVE, d // 2, ac))
                p = d // 2
            adt = ac = 0
        adt += tail[0]
        ac += tail[1]
    return (new, (adt, ac)) if p == p0 else None


def lean_plan(k, passes):
    """The plan for lean/CascadeRun.lean (tables for k levels, then `passes` passes of the last one) and the super
    step and machine step where it ends."""
    plan = []
    end = [row for row in run(float("inf"), max_k=k, plan=plan, last_passes=passes) if row[0] == "end"][0]
    return plan, end[1], end[2]


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(__doc__)
    elif sys.argv[1] == "plan":
        plan, S, T = lean_plan(int(sys.argv[2]), int(sys.argv[3]))
        print("[" + ", ".join(f"({r}, {L})" for r, L in plan) + "]")
        print(S)
        print(T)
    else:
        for row in run(int(float(sys.argv[1]))):
            print(*row)
