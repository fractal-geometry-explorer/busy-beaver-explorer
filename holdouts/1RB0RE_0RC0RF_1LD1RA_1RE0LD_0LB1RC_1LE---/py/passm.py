"""The pass machine of lean/General.lean in Python, move for move (`pstep`, `sub`), and its check against the machine.

A moment is (bs, l, us) as `gcfg bs l us` in Lean: the head in C on a 0, the last block l on its left, the blocks bs
before it (nearest first, any sizes, blank tape after the last) and the zone gaps us on its right (the first gap
not counting the head's cell).  `sub(bs, l, us)` is one sub-round: ("moment", bs', l', us', steps) or ("halt",).

usage: python3 py/passm.py check N     N random tapes: `sub` against the machine (py/model.py), steps included
"""
import os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def hd(x, d=0):
    return x[0] if x else d


def rd(us):
    return [] if not us else ([0] + us[1:] if us[0] == 0 else [us[0] - 1] + us[1:])


def pstep(s):
    """one move: ("next", s', n) | ("done", bs, l, us, n) | ("halt",); s = (lb, ph, k, us)"""
    lb, ph, k, us = s
    if ph == "A" and k >= 3:
        a = k // 3
        return "next", ([2] * a + lb, "A", k % 3, us), 3 * a
    if k >= 1:
        if ph == "A": return "next", ([0] + lb, "E", k - 1, us), 1
        nph = "C" if ph == "E" else "A"
        return "next", ([hd(lb) + 1] + lb[1:], nph, k - 1, us), 1
    if us and us[0] == 0:
        return "next", (lb, ph, 1, us[1:]), 0
    t = lb[1:]
    if ph == "C":
        if hd(lb) == 0: return "next", ([hd(t) + 2] + t[1:], "C", 0, rd(us)), 3
        return "done", t, hd(lb), rd(us), 0
    if ph == "E":
        if hd(lb) == 0: return "next", ([hd(t) + 2] + t[1:], "C", 0, rd(us)), 5
        return "next", ([hd(t) + 3] + t[1:], "A", hd(lb) - 1, rd(us)), 3 * (hd(lb) - 1) + 9
    # A on a 0
    if not us: return "next", ([hd(lb) + 3] + lb[1:], "C", 0, []), 5
    if us[0] >= 3: return "next", ([hd(lb) + 3] + lb[1:], "C", 0, [us[0] - 3] + us[1:]), 5
    if us[0] == 2: return "next", ([1, hd(lb) + 1] + lb[1:], "A", 0, us[1:]), 3
    if len(us) > 1 and us[1] == 0: return ("halt",)
    return "next", ([hd(t) + 3] + t[1:], "A", hd(lb) + 1, rd(us[1:])), 3 * hd(lb) + 12


def sub(bs, l, us, fuel=10 ** 6, moves=None):
    """one sub-round from gcfg bs l us"""
    if not bs or bs[0] < 1 or l < 1: return ("stuck",)
    p, rest = bs[0], bs[1:]
    s = ([hd(rest) + 3] + rest[1:], "A", p, [l - 1] + list(us)); n = (l - 1) + 3 * (p - 1) + 15
    for _ in range(fuel):
        r = pstep(s)
        if moves is not None: moves.append(r[0] if r[0] != "next" else "next")
        if r[0] == "next": s = r[1]; n += r[2]
        elif r[0] == "done": return "moment", r[1], r[2], r[3], n + r[4]
        else: return ("halt",)
    return ("stuck",)


def to_model(bs, l, us):
    """(blocks far..near incl. l, python gaps with the head's cell) for py/model.py"""
    return list(reversed(bs)) + [l], ([us[0] + 1] + us[1:]) if us else []


def sub_fast(bs, l, us):
    """`sub` with the blocks kept far end first (a stack), so that a move costs O(1); same results as `sub`"""
    if not bs or bs[0] < 1 or l < 1: return ("stuck",)
    st = list(reversed(bs[1:]))            # stack: the nearest block last
    def pop():
        return st.pop() if st else 0
    c = pop(); st.append(c + 3)
    ph, k, us = "A", bs[0], [l - 1] + list(us); n = (l - 1) + 3 * (bs[0] - 1) + 15; j = 0   # us read from index j
    def u0(): return us[j] if j < len(us) else None
    def rdz():
        nonlocal j
        if j >= len(us): return
        if us[j] > 0: us[j] -= 1
    while True:
        if ph == "A" and k >= 3:
            a = k // 3; st.extend([2] * a); k %= 3; n += 3 * a; continue
        if k >= 1:
            if ph == "A": st.append(0); ph = "E"
            else: st.append(pop() + 1); ph = "C" if ph == "E" else "A"
            k -= 1; n += 1; continue
        u = u0()
        if u == 0: k = 1; j += 1; continue
        if ph == "C":
            o = pop()
            if o == 0: st.append(pop() + 2); rdz(); n += 3; continue
            rdz(); return "moment", list(reversed(st)), o, us[j:], n
        if ph == "E":
            o = pop()
            if o == 0: st.append(pop() + 2); ph = "C"; rdz(); n += 5; continue
            st.append(pop() + 3); ph = "A"; k = o - 1; rdz(); n += 3 * (o - 1) + 9; continue
        if u is None or u >= 3:
            st.append(pop() + 3); ph = "C"; n += 5
            if u is not None: us[j] -= 3
            continue
        if u == 2:
            st.append(pop() + 1); st.append(1); j += 1; n += 3; continue
        if j + 1 < len(us) and us[j + 1] == 0: return ("halt",)
        o = pop(); st.append(pop() + 3); k = o + 1; j += 1; rdz(); n += 3 * o + 12


def trans_pass(I, l, gaps, R=40, maxsteps=10 ** 11):
    """c/trans.c with the pass machine in place of the machine: sub-rounds until a moment that c/trans.c stops at"""
    import model
    bs = list(reversed(I)); us = ([gaps[0] - 1] + gaps[1:]) if gaps else []
    steps = 0
    while steps < maxsteps:
        r = sub_fast(bs, l, us)
        if r[0] == "halt": return "HALT", steps, None, None, None
        if r[0] != "moment": return "max", steps, None, None, None
        _, bs, l, us, n = r; steps += n
        I2 = list(reversed(bs)); g = ([us[0] + 1] + us[1:]) if us else []
        if not (model.regular_interior(I2) and model.regular_last(l)): continue
        segs, rest, full = model.split(g)
        if full: return "reg", steps, I2, l, g
        if segs:
            m, rem = model.dec(l, segs)
            if rem - 1 >= R: return "part", steps, I2, l, g
    return "max", steps, None, None, None


if __name__ == "__main__" and sys.argv[1] == "hybrid":
    import model
    K = int(sys.argv[2]); orig = model.trans; calls = bad = 0; tot = [0]
    def both(I, l, gaps, R=40, maxsteps=10 ** 11):
        global calls, bad
        a = orig(I, l, gaps, R, maxsteps); b = trans_pass(I, l, gaps, R, maxsteps); calls += 1
        if (a[0], a[1], a[2], a[3], a[4]) != b:
            bad += 1; print("DIFFERENT", model.rle(I[-8:]), l, gaps[:8], a[:2], b[:2])
        return a
    model.trans = both
    st, nreb, subs, dsteps = model.run(*model.START, K, verbose=False)
    print(f"{st}: {nreb} rebuilds, {calls} stretches simulated directly ({dsteps} machine steps): the pass machine "
          f"gives the same configuration and step count in {calls - bad}")
    sys.exit(1 if bad else 0)


if __name__ == "__main__" and sys.argv[1] == "check":
    import model
    N = int(sys.argv[2]); random.seed(7); bad = tested = halts = 0
    for _ in range(N):
        bs = [random.randint(1, 14) for _ in range(random.randint(1, 5))]
        l = random.randint(1, 12)
        us = [random.randint(0, 9) for _ in range(random.randint(0, 6))]
        blocks, gaps = to_model(bs, l, us)
        if not gaps: gaps = [1]  # head cell only, then blank: Lean us = []
        r = model.sub_round(blocks, gaps if us else [], 10 ** 6)
        m = sub(bs, l, us)
        if m != sub_fast(bs, l, us): bad += 1; print("sub_fast differs", bs, l, us)
        if r[0] == "max": continue
        tested += 1
        if r[0] == "HALT":
            halts += 1; bad += m[0] != "halt"; continue
        mb, mg = r[2]
        ok = m[0] == "moment" and to_model(m[1], m[2], m[3])[0] == mb and m[4] == r[1]
        if ok:
            g = to_model(m[1], m[2], m[3])[1]
            # trailing blank: model.read drops zeros after the last 1
            ok = g == mg or (not m[3] and mg == [])
        if not ok:
            bad += 1
            if bad < 10: print("DIFFERENT", bs, l, us, "machine", r, "pass", m)
    print(f"{tested} random tapes: the pass machine and the machine differ on {bad} ({halts} halt)")
    sys.exit(1 if bad else 0)
