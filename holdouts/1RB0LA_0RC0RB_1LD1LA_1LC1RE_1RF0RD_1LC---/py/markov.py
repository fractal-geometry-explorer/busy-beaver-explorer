"""The halting heuristic of 1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---: the context as a Markov chain driven by fair
bits b = ceil(n/2) mod 2.

Why fair bits: n' = (3n + d)/2 with d fixed by (c, n mod 4), so n mod 2^(k+1) fixes the next k bits, and each of the
2^k bit strings comes from exactly two residues of n mod 2^(k+1), for every starting context (`bits` below checks
this for k <= 14).  The bits used at pass i are bits of n_0 that no earlier pass looked at; nothing about the size of
n enters.  So the chance of a halt is a fixed rate per pass, the absorption rate of this chain.

usage: python3 markov.py rate T         propagate the distribution from '1' for T passes: halting rate per pass,
                                         the halting (context, bit) pairs that carry it, the quasi-stationary
                                         distribution (compare with the orbit's context counts, c/orbit.c)
       python3 markov.py bits K         check the bijection n mod 2^(K+1) -> (b_0..b_(K-1)) from a few contexts
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import emap  # noqa: E402

R = {0: 3, 1: 1}   # a residue mod 4 with this bit


def nxt(c, b):
    return emap.rule(c, R[b])[0]


if __name__ == "__main__":
    try:
        if sys.argv[1] == "rate":
            T = int(sys.argv[2])
            P, tot = {"1": 1.0}, 0.0
            for t in range(T):
                Q, h, hp = {}, 0.0, {}
                for c, p in P.items():
                    for b in (0, 1):
                        c2 = nxt(c, b)
                        if c2 == "HALT":
                            h += p / 2
                            hp[(c, b)] = hp.get((c, b), 0) + p / 2
                        else:
                            Q[c2] = Q.get(c2, 0) + p / 2
                s = sum(Q.values())
                P = {c: p for c, p in Q.items() if p >= 1e-30 * s}
                tot += h
            s = sum(P.values())
            rate = h / (s + h)
            print(f"rate: {len(P)} contexts; halting rate per pass {rate:.4e} (mean {1 / rate:.3e} passes); "
                  f"absorbed after {T} passes {tot:.3e}")
            print("halting pairs (context, bit): share of the rate")
            for (c, b), p in sorted(hp.items(), key=lambda x: -x[1])[:12]:
                print(f"   {c} b={b}: {p / h:.3f}   (quasi-stationary probability of {c}: {P.get(c, 0) / s:.3e})")
            print("quasi-stationary distribution (top 25):")
            print(" ".join(f"{c}:{p / s:.4e}" for c, p in sorted(P.items(), key=lambda x: -x[1])[:25]))
        elif sys.argv[1] == "bits":
            K = int(sys.argv[2])
            for c0 in ("1", "11", "10001", "11011"):
                seen = {}
                for n0 in range(2 ** (K + 1), 2 ** (K + 2)):
                    c, n, bits = c0, n0, ""
                    for _ in range(K):
                        r = n % 4
                        bits += "1" if r in (1, 2) else "0"
                        c2, d = emap.rule(c, r)[:2]
                        if c2 == "HALT":
                            # continue the count with any next context: the bit is what matters here
                            c2, d = c, emap.rule(c, (r + 2) % 4)[1] if emap.rule(c, (r + 2) % 4)[0] != "HALT" else 0
                            break
                        c, n = c2, (3 * n + d) // 2
                    else:
                        seen[bits] = seen.get(bits, 0) + 1
                ok = len(seen) == 2 ** K and set(seen.values()) == {2}
                print(f"bits: context {c0}, K = {K}: {len(seen)} bit strings, each from {sorted(set(seen.values()))}"
                      f" residues mod 2^{K + 1}: {'bijection' if ok else 'NOT uniform (a halt cut some orbits)'}")
    finally:
        emap.save()
