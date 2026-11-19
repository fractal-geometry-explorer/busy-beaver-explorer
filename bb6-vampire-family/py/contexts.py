"""Choose the contexts of each variant's Lean table (writes contexts.txt).

The table holds (1) every context the orbits of the variant's holdouts use in their first 2^30 passes, as counted
by c/orbit.c (files given on the command line), and (2) every context whose weight in the Markov
model (fair bits, propagated from `1` for T passes) is at least 1e-13 in some pass, which includes the contexts whose
halting entries carry the halting rate.  Prints the halting rate per pass and the halting entries by weight.

usage: python3 contexts.py T orbit.out...      (the c/orbit.c outputs of the seven machines)
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import family as fam  # noqa: E402

THRESH = 1e-13


def used(fn):
    out = {}
    for line in open(fn):
        if line.startswith("contexts used"):
            for tok in line.split(":", 1)[1].split():
                c, k = tok.rsplit(":", 1)
                out[c] = out.get(c, 0) + int(k)
    return out


if __name__ == "__main__":
    T = int(sys.argv[1])
    cnt = {}
    for fn in sys.argv[2:]:
        for c, k in used(fn).items():
            cnt[c] = cnt.get(c, 0) + k
    # the rewrites never read F0 (gen.py checks this for every table entry), so the Markov model is the same
    f0 = "1LC"
    P, keep, hp = {"1": 1.0}, set(cnt), {}
    rate = 0.0
    for t in range(T):
        Q, h = {}, 0.0
        for c, p in P.items():
            if p >= THRESH:
                keep.add(c)
            for b in (0, 1):
                r = fam.rule(f0, c, b)
                if r == "HALT":
                    h += p / 2
                    hp[(c, b)] = hp.get((c, b), 0) + p / 2
                else:
                    Q[r[0]] = Q.get(r[0], 0) + p / 2
        s = sum(Q.values())
        rate = h / (s + h)
        P = {c: p / s for c, p in Q.items() if p / s > 1e-30}
    tot = sum(hp.values())
    print(f"halting rate per pass {rate:.4g}; {len(keep)} contexts in the table", file=sys.stderr)
    for (c, b), p in sorted(hp.items(), key=lambda x: -x[1])[:6]:
        print(f"  halt {c} b={b}: {p / tot:.4f} of the halting mass, in table: {c in keep}", file=sys.stderr)
    fn = os.path.join(os.path.dirname(os.path.abspath(__file__)), "contexts.txt")
    with open(fn, "w") as fh:
        fh.write(f"# contexts of the Lean table: those the seven orbits use in their first 2^30 passes (with counts, "
                 f"c/orbit.c), and those of Markov weight >= {THRESH:g} within {T} passes from 1 (count 0)\n")
        for c in sorted(keep, key=lambda c: (-cnt.get(c, 0), len(c), c)):
            fh.write(f"{c} {cnt.get(c, 0)}\n")
