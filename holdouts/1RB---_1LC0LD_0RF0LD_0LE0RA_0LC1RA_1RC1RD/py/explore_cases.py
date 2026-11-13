"""Find, for every tail and residue, the forms of the E-event map that the symbolic prover can do in one go:
start E(8m+8+r, F(t+K)), the super-round loop m times, then straight to the next E-event.  Prints a table.
(Exploration helper for gen_map.py.)"""
import sys
import chain as C
import emap

M = emap.M


def tl(F, t):
    return {"1": "1", "X": f"0 0 0 (10)^{t} 1", "Y": f"1 1 (01)^{t}", "Z": f"0 0 0 (10)^{t} 0 0 0 1"}[F]


def ev(n, F, t):
    return f"0^inf E> 0 0 0 0 0 0 (10)^{n} {tl(F, t)} 0^inf"


def fit(f):
    """f(m, t) -> (F', t', n'); returns (F', t' lin, n' lin) as strings 'a*m+b*t+c' if linear in m, t"""
    pts = [(m, t) for m in (3, 4, 5) for t in (5, 6, 7)]
    outs = [f(m, t) for m, t in pts]
    if any(o is None or o == "HALT" for o in outs) or len({o[0] for o in outs}) != 1:
        return None
    res = [outs[0][0]]
    for j in (1, 2):
        v = {p: o[j] for p, o in zip(pts, outs)}
        a = v[(4, 5)] - v[(3, 5)]
        b = v[(3, 6)] - v[(3, 5)]
        c = v[(3, 5)] - 3 * a - 5 * b
        if any(v[(m, t)] != a * m + b * t + c for m, t in pts):
            return None
        res.append((a, b, c))
    return res


def lin_str(a, b, c, m="m", t="t"):
    parts = []
    if a:
        parts.append(f"{a}*{m}" if a != 1 else m)
    if b:
        parts.append(f"{b}*{t}" if b != 1 else t)
    s = "+".join(parts)
    if c or not s:
        s = (s + ("+" if c >= 0 else "") + str(c)) if s else str(c)
    return s


if __name__ == "__main__":
    lib = C.Lib(M, "H70770")
    loops = {}
    for F, tw in (("X", "0 0 0 (10)^t 1"), ("Y", "1 1 (01)^t+1")):
        loops[F] = C.Loop(lib, "sr" + F, f"0^inf (10)^9*i+3 E> (10)^8*x+8+r {tw} 0^inf")
    for F in "XY":
        for r in range(8):
            for K in range(0, 4):
                f = lambda m, t: emap.step(F, t + K, 8 * m + 8 + r)
                e = fit(f)
                if e is None:
                    print(F, r, K, "not linear")
                    continue
                F2, tt, nn = e
                end = ev(lin_str(*nn), F2, lin_str(*tt) if F2 != "1" else "0")
                c = C.Case(lib, f"c{F}{r}_{K}", ev(f"8*m+8+{r}", F, f"t+{K}"))
                try:
                    if F == "Y":
                        if K == 0:
                            raise C.S.ProofError("Y with t = 0 uses the Y0 loop")
                        c.loop(loops[F], "m", "0", "0", r=r, t=f"t+{K - 1}")
                    else:
                        c.loop(loops[F], "m", "0", "0", r=r, t=f"t+{K}")
                    c.emit(end, "(m t : Nat)")
                    print(F, r, K, "OK ->", F2, tt, nn, flush=True)
                    break
                except (C.S.ProofError, ValueError) as ex:
                    print(F, r, K, "fail", str(ex)[:150], flush=True)
