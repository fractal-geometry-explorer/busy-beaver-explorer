"""The stopping rule of this machine's rebuild as a walk over the digits of N, and its checks.

At a V = 0 moment the tape is `0^inf 1 U 00 E> 0110101 (11)^n 1 0^inf`; N is the up-counter with its sentinel read
as one binary number (see ../../1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py/rebuild.py).  The rebuild reads N's
digits b0, b1, ... from the bottom:

    b0 = 0                      stop, j = 1
    b0 = 1                      go on in state Q with the pairs (b1, b2), (b3, b4), ...
    Q:  (1, 1) -> Q    (0, 0) -> R    (0, 1), (1, 0) -> stop
    R:  (x, 0) -> R    (x, 1) -> stop

If it stops on its k-th pair it has read j = 2k + 1 digits.  Then (observed, see `check`) the new up-counter is
N >> j, the header stays 0110101 and V gets c = (5j + 1)/2 more digits: V' = 2^(n + c) - delta, delta a function
of the j digits read.  The next macro state is (n + c, 2^(n + c) + (N >> j) - delta).

In words: Q runs through ones and R through zeros; R stops at the first 1 in an even position (b0 at position 0).

usage: python3 walk.py check B            every N < 2^B, n - len(N) + 1 in {0, 1}, against the exact rebuild
       python3 walk.py random T B         T random N of B digits
       python3 walk.py run SECONDS        the macro run from blank tape, every rebuild against the walk, and how
                                          close the walk comes to the top of N
       python3 walk.py top B              what the rebuilds not covered by the walk (N < 2^B) do
"""
import os, sys, random, math, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB", "py"))
M = "1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---"
H0 = "0110101"


def walk(N):
    """j, the number of digits read, or None if the walk does not stop below the top digit of N"""
    L = N.bit_length()
    if N & 1 == 0: return 1
    s = "Q"; k = 0
    while 2 * k + 2 < L:
        x = (N >> (2 * k + 1)) & 1; y = (N >> (2 * k + 2)) & 1; k += 1
        if s == "Q":
            if x != y: return 2 * k + 1
            s = "Q" if x else "R"
        elif y: return 2 * k + 1
    return None


def covered(N):
    """the walk stops and leaves at least two digits (the sentinel and one more)"""
    j = walk(N)
    return j is not None and j <= N.bit_length() - 2


def predict(n, N):
    j = walk(N)
    return (H0, n + (5 * j + 1) // 2, N >> j)


def compare(rb, n, N):
    r = rb.rebuild(H0, n, N, maxd=10 ** 9)
    if not covered(N): return "top", r
    if r[0] != "OK": return "bad", r
    H2, n2, N2, V2, f2, L2 = r[2]
    return ("ok" if (H2, n2, N2) == predict(n, N) else "bad"), r


def main():
    from rebuild import Rebuilder, macro_run
    rb = Rebuilder(M); cmd = sys.argv[1]
    if cmd in ("check", "random"):
        cnt = collections.Counter(); bad = []
        if cmd == "check":
            B = int(sys.argv[2])
            cases = ((N.bit_length() - 1 + d, N) for N in range(2, 1 << B) for d in (0, 1) if N.bit_length() - 1 + d >= 1)
            what = f"N < 2^{B}, n - len(N) + 1 in {{0, 1}}"
        else:
            T, B = int(sys.argv[2]), int(sys.argv[3]); random.seed(1)
            cases = [(B + random.randint(-1, 0), (1 << (B - 1)) | random.getrandbits(B - 1)) for _ in range(T)]
            what = f"{T} random N of {B} digits"
        jmax = 0
        for n, N in cases:
            res, r = compare(rb, n, N); cnt[res] += 1
            if res == "bad": bad.append((n, N, str(r)[:200]))
            if res == "ok": jmax = max(jmax, walk(N))
        print(f"{what}: {cnt['ok']} rebuilds follow the walk (longest j = {jmax}), {cnt['top']} have a walk that "
              f"reaches the top two digits of N (not covered), {len(bad)} contradict it")
        for x in bad[:20]: print("  ", x)
        sys.exit(1 if bad else 0)
    if cmd == "top":
        B = int(sys.argv[2]); cnt = collections.Counter()
        for N in range(2, 1 << B):
            for d in (0, 1):
                n = N.bit_length() - 1 + d
                if n < 1 or covered(N): continue
                r = rb.rebuild(H0, n, N, maxd=10 ** 9)
                cnt[(r[0], r[2][0] if r[0] == "OK" else "")] += 1
        print(f"N < 2^{B}, walk not covered:", dict(cnt))
        return
    if cmd == "run":
        secs = float(sys.argv[2])
        st = dict(prev=None, ok=0, bad=[], jmax=0, margin=None, ones=None, k=0, steps=0, n=0)
        hist = collections.Counter()

        def o(x):
            if x[0] == "start":
                st["first"] = (x[1], x[2], x[3]); return
            if x[0] in ("HALT", "STUCK"):
                st["bad"].append(x); return
            it, H, n, N, form, steps, rs, subs, N2, d = x
            if st["prev"] is None:                     # the first rebuild starts from header 0110111
                st["prev"] = (n, N); return
            n0, N0 = st["prev"]
            if covered(N0) and (H, n, N2) == predict(n0, N0):
                j = walk(N0); st["ok"] += 1; st["jmax"] = max(st["jmax"], j); hist[j] += 1
                if it >= 10:
                    m = N0.bit_length() - j; q = bin(N0 >> j).count("1") - 1
                    st["margin"] = m if st["margin"] is None else min(st["margin"], m)
                    st["ones"] = q if st["ones"] is None else min(st["ones"], q)
                    if it % 1000 == 0: st.setdefault("samples", []).append((it, N0.bit_length(), bin(N0).count("1")))
            else:
                st["bad"].append((it, n0, walk(N0)))
            st["prev"] = (n, N); st["k"] = it; st["steps"] = steps; st["n"] = n
        macro_run(M, 10 ** 9, secs, o)
        print(f"first V = 0 moment: header {st['first'][0]}, n = {st['first'][1]}, N = {st['first'][2]}; after its "
              f"rebuild the header is 0110101 for good")
        print(f"macro run: {st['k'] + 1} rebuilds, about 10^{st['steps'].bit_length() * math.log10(2):.0f} steps, "
              f"V has {st['n']} digits; {st['ok']} rebuilds follow the walk, {len(st['bad'])} do not")
        print(f"longest walk j = {st['jmax']}; from rebuild 10 on the walk always stops at least {st['margin']} "
              f"digits and {st['ones']} ones below the sentinel")
        print("digits read:", ", ".join(f"j={j}: {c}" for j, c in sorted(hist.items())))
        print("(rebuild, digits of N, ones in N):", st.get("samples"))
        for x in st["bad"][:10]: print("  ", str(x)[:300])
        sys.exit(1 if st["bad"] else 0)


if __name__ == "__main__":
    main()
