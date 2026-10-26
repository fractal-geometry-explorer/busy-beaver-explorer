"""Rigorous 2-adic refinement of the clean-tape cycle.
A class n = rho (mod 2^k) is run with n = 2^k j + rho, j large and otherwise free: every position is alpha*j + beta.
A swap/merge test is decided when alpha = 0 (mod 4); otherwise the class splits on the next binary digit of n.
A settled class has the same cycle for every large j: same jump, rounds and right-end chain (as defined in model.c)."""
import sys, json

class NeedBit(Exception): pass
class Halt(Exception): pass

def mod4(d):
    a, b = d
    if a % 4: raise NeedBit()
    return b % 4

def cycle(k, rho, max_rounds=3000):
    """Returns ('settled', jump, rounds, chain) or ('split',) ; positions are (alpha, beta) tuples."""
    add = lambda p, c: (p[0], p[1] + c)
    half = lambda p: (p[0] // 2, p[1] // 2)
    w0 = (2 ** (k + 1), 2 * rho + 6)
    w = w0; marks = [["G", (0, 1)], ["M", add(w0, -2)]]
    endd = []
    for rounds in range(1, max_rounds + 1):
        marks.sort(key=lambda m: m[1])
        gap = marks[0]
        def first_right(x):
            r = [m for m in marks if m[1] > x]
            return min(r, key=lambda m: m[1]) if r else None
        def last_mark():
            return max(marks, key=lambda m: m[1])
        def packet_back(x):
            left = [m for m in marks if m[1] < x and m[0] != "M"]
            if not left: return None
            m = max(left, key=lambda m: m[1])
            if m[0] == "B": raise Halt()
            if m[0] == "G": m[1] = add(m[1], 2); return m
            q = m[1]; m[0], m[1] = "M", add(q, -1)
            g = ["G", add(q, 1)]; marks.append(g); return g
        def shift_from(x):
            nonlocal w
            kk = first_right(x)
            if kk is None:
                w = add(w, 2); marks.append(["M", add(w, -2)]); return packet_back(add(w, -2))
            if kk[0] == "M": kk[0] = "G"; return kk
            if kk[0] == "W": kk[0] = "B"; return packet_back(kk[1])
            if kk[0] == "B": kk[0] = "W"; kk[1] = add(kk[1], 2); return packet_back(kk[1])
            raise RuntimeError("shift into " + kk[0])
        while gap is not None:
            g = gap[1]; m = first_right(g)
            if m is None:
                marks.remove(gap); w = add(w, 3); marks.append(["M", add(w, -2)]); gap = packet_back(add(w, -2)); continue
            if m[0] == "M":
                d = (m[1][0] - g[0], m[1][1] - g[1] - 3)
                r4 = mod4(d)
                if r4 % 2: raise RuntimeError("odd distance")
                if m is last_mark(): endd.append((d, r4))
                if r4 == 0:
                    h = half(d); m[1] = (g[0] + h[0], g[1] + h[1] - 1); gap[1] = (g[0] + h[0], g[1] + h[1] + 1)
                else:
                    h = half(d); marks.remove(gap); m[0], m[1] = "W", (g[0] + h[0], g[1] + h[1] + 3); gap = packet_back(m[1])
            elif m[0] == "W":
                x = m[1]; marks.remove(gap); marks.remove(m); gap = shift_from(x)
            elif m[0] == "B":
                m[0], m[1] = "W", add(m[1], -1); gap = shift_from(m[1])
            else:
                raise RuntimeError("gap meets " + m[0])
        extra = 2
        for mm in marks:
            if mm[0] == "M" and mm[1] == (0, 0): mm[0], mm[1] = "W", (0, 1); extra = 4
        marks = [[t, add(p, extra)] for t, p in marks] + [["G", (0, 1)]]
        w = add(w, extra)
        if len(marks) == 2 and any(t == "M" and p == add(w, -2) for t, p in marks):
            assert w[0] == w0[0]
            best = cur = 1 if endd else 0
            for (d0, r0), (d1, r1) in zip(endd, endd[1:]):
                pd = ((d0[0] - 0) // 2, (d0[1] - 2) // 2) if r0 == 2 else (d0[0] // 2, d0[1] // 2 + 4)
                if d1 == pd: cur += 1; best = max(best, cur)
                else: cur = 1
            return ("settled", (w[1] - w0[1]) // 2, rounds, best)
    return ("long",)

def refine(K, cap=None, report=None):
    """Level by level: classes mod 2^k that are not yet settled are split into two."""
    cur = [(1, 0), (1, 1)]           # (k, rho) with k digits known
    stats = []
    settled_all = []
    for k in range(1, K + 1):
        nxt = []; settled = []; halts = []
        for kk, rho in cur:
            try:
                out = cycle(kk, rho)
            except NeedBit:
                nxt += [(kk + 1, rho), (kk + 1, rho + 2 ** kk)]; continue
            except Halt:
                halts.append(rho); continue
            if out[0] == "settled": settled.append((kk, rho) + out[1:])
            else: nxt += [(kk + 1, rho), (kk + 1, rho + 2 ** kk)]
        settled_all += settled
        stats.append(dict(k=k, settled=len(settled), unsettled=len(nxt) // 2, halts=halts,
                          maxchain=max([s[4] for s in settled], default=0)))
        if report: report(stats[-1], settled)
        cur = nxt
        if cap and len(cur) > cap: break
    return stats, settled_all, cur

if __name__ == "__main__":
    K = int(sys.argv[1])
    def rep(st, settled):
        print(f"digits {st['k']:2d}: settled {st['settled']:7d}  still open {st['unsettled']:7d}  "
              f"longest chain among newly settled {st['maxchain']:2d}  halting classes {len(st['halts'])}", flush=True)
    stats, settled, open_ = refine(K, report=rep)
    json.dump([list(s) for s in settled], open(f"nrefine_{K}.json", "w"))
    json.dump([list(c) for c in open_], open(f"nrefine_{K}_open.json", "w"))
