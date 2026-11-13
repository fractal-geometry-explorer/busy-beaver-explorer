"""Two exhaustive checks of the rebuild map and one statistic of the macro run.

  python3 rebuild_stats.py MACHINE halting B       every N < 2^B, for each (header, top-word form, n - len(N) + 1)
                                                  that the first 20 s of the macro run from blank tape produce:
                                                  which rebuilds halt (prints them, and whether every one is N =
                                                  all ones)
  python3 rebuild_stats.py MACHINE shape B        the same inputs, for the rebuilds that do not halt: the kinds of
                                                  N' (N >> j for some j, or other) and whether N' - delta = -1
  python3 rebuild_stats.py MACHINE run SECONDS     the macro run from blank tape with, per rebuild: j (digits
                                                  consumed), c (digits added to V), len(delta), len(N'), n - len(N)
"""
import os, sys, time, math, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rebuild import Rebuilder, macro_run

def seen(M, secs=20):
    """the (header, form of the top word, n - len(N) + 1) of the V=0 moments in the first SECS seconds of the run"""
    out = set()

    def o(x):
        if x[0] == "start": out.add((x[1], x[4], x[2] - x[3].bit_length() + 1))
        elif x[0] not in ("HALT", "STUCK"): out.add((x[1], x[4], x[2] - x[3].bit_length() + 1))
    macro_run(M, 10 ** 9, secs, o)
    return sorted(out)


def inputs(rb, B, kinds):
    for H, form, d in kinds:
        lo = 2 if form == "1" else 4 if form == "1000" else 1
        for N in range(lo, 1 << B):
            yield H, form, d, N


def all_ones(N):
    return N & (N + 1) == 0


def main():
    M, cmd = sys.argv[1], sys.argv[2]
    rb = Rebuilder(M)
    if cmd in ("halting", "shape"):
        B = int(sys.argv[3])
        ks = seen(M)
        print("(header, form, n - len(N) + 1) seen in the run:", ks)
        halts = []; kinds = collections.Counter(); minus1 = []
        for H, form, d, N in inputs(rb, B, ks):
            if True:
                n = N.bit_length() - 1 + d
                if n < 1: continue
                r = rb.rebuild(H, n, N, form, maxd=10 ** 8)
                if r[0] != "OK":
                    halts.append((H, N, n, r[0], r[1])); continue
                H2, n2, N2, V2, f2, L2 = r[2]
                dl = (1 << n2) - V2
                j = N.bit_length() - N2.bit_length()
                kinds["N>>j" if j > 0 and N >> j == N2 else f"other {N2}"] += 1
                if N2 - dl == -1: minus1.append((H, N, n, H2, n2))
        if cmd == "halting":
            for h in halts: print("halt" if h[3] == "HALT" else h[3], h[0], bin(h[1]), "n =", h[2], "steps", h[4])
            print(f"{len(halts)} of the rebuilds with N < 2^{B} of these kinds halt; all of them N = all ones: "
                  f"{all(all_ones(h[1]) for h in halts)}")
        else:
            print(dict(kinds)); print("N' - delta = -1:", minus1)
    elif cmd == "run":
        secs = float(sys.argv[3]); t0 = time.time()
        prev = {}

        def show(x):
            if x[0] == "start":
                prev["N"] = x[3]; prev["n"] = x[2]; return
            if x[0] in ("HALT", "STUCK"):
                print(x[0], x[1:3], flush=True); return
            it, H, n, N, form, steps, rs, subs, N2, d = x
            H = H + "/" + form
            Np = prev["N"]
            j = Np.bit_length() - N2.bit_length()
            kind = "pre" if j > 0 and Np >> j == N2 else f"N'={N2}" if N2 < 64 else "other"
            print(f"{it} {H} n={n} dn={n - prev['n']} lenN_in={Np.bit_length()} n_in-len+1={prev['n'] - Np.bit_length() + 1} "
                  f"j={j} {kind} len(delta)={d.bit_length()} len(N')={N2.bit_length()} "
                  f"log10steps={steps.bit_length() * math.log10(2):.1f} t={time.time() - t0:.0f}", flush=True)
            prev["N"] = N; prev["n"] = n
        macro_run(M, 10 ** 9, secs, show)


if __name__ == "__main__":
    main()
