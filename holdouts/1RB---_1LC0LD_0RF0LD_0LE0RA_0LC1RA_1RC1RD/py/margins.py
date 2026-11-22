"""Long run of the E-event map of emap.py from blank tape, with margin statistics at the Z-events.

    python3 margins.py N [EVERY]       N map steps from (1, 0); a line every EVERY steps (default 10^5)

At each Z-event (Z_k, n) the margin is n/(12k+12) (the map needs it >= 1).  Each line gives the pass count, the
number of decimal digits of n, the Z-events so far, the largest k so far, the smallest margin in the last block
(log10), and the largest k at a Z-event in the last block.  The last line summarises the run."""
import math
import sys

from emap import step


def log10(x):
    b = x.bit_length()
    if b < 1000:
        return math.log10(x)
    return math.log10(x >> (b - 60)) + (b - 60) * math.log10(2)


def run(N, every):
    f, k, n = "1", 0, 0
    zs = kmax = 0
    best = (None, 0, 0, 0)  # (log10 margin, pass, k, n digits)
    blk_min, blk_kz = None, 0
    phases = 0
    hist = {}
    for i in range(1, N + 1):
        if f == "Z":
            zs += 1
            hist[k] = hist.get(k, 0) + 1
            m = log10(n) - math.log10(12 * k + 12)
            if blk_min is None or m < blk_min:
                blk_min = m
            if best[0] is None or m < best[0]:
                best = (m, i - 1, k, int(log10(n)) + 1)
            blk_kz = max(blk_kz, k)
        r = step(f, k, n)
        if r is None:
            print("NOT COVERED at pass", i - 1, f, k, "n with", int(log10(n)) + 1, "digits", flush=True)
            return
        if r[0] == "1" and f != "1":
            phases += 1
        f, k, n = r
        kmax = max(kmax, k)
        if i % every == 0:
            print(f"{i} digits={int(log10(n)) + 1} Z={zs} phases={phases} kmax={kmax} "
                  f"blockmin_log10margin={blk_min if blk_min is None else round(blk_min, 1)} blockmax_kZ={blk_kz}",
                  flush=True)
            blk_min, blk_kz = None, 0
    print(f"DONE {N} passes from (1, 0), all covered by the map. n has {int(log10(n)) + 1} digits; "
          f"{zs} Z-events, {phases} returns to tail 1, largest k {kmax}; smallest margin 10^{best[0]:.2f} "
          f"at pass {best[1]} (k = {best[2]}).", flush=True)
    top = sorted(hist.items())[-10:]
    print("largest k at Z-events (k: count):", top, flush=True)
    ks = sorted(hist)
    for K in (10, 30, 100, 300, 1000, 3000):
        c = sum(v for kk, v in hist.items() if kk >= K)
        print(f"Z-events with k >= {K}: {c} ({c / max(zs, 1):.2e})", flush=True)


if __name__ == "__main__":
    run(int(float(sys.argv[1])), int(float(sys.argv[2])) if len(sys.argv) > 2 else 10**5)
