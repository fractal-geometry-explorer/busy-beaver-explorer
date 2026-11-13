"""The stopping rule of the rebuild as a walk over the digits of N, and its checks against the exact rebuild.

At a V = 0 moment the macro state is (H, n, N) (see rebuild.py).  The rebuild reads N's binary digits from the bottom
in pairs (b1 b0), (b3 b2), ... and moves a 4-state automaton O, P, Q, R; header 0110101 starts it in O, header 0110111
in Q.  Writing a pair as the number 2 b_{2i+1} + b_{2i} (00, 01, 10, 11):

        00  01  10  11
    O   P   *   Q   O          * = stop
    P   P   P   *   Q
    Q   R   P   P   Q
    R   R   R   P   P

If the walk stops on its k-th pair it has read j = 2k + 1 digits: the k pairs and one more digit b = b_{2k}.  Then
(observed) the up-counter becomes N' = N >> j, the new header is 0110101 if b = 0 and 0110111 if b = 1, and V gets
c = (5j + 1)/2 more digits: V' = 2^(n + c) - delta with delta = delta0 - b.  delta0 depends on all the digits read
(not only on the automaton's path; it grows like 4^(length of the runs of 00 and 11 pairs)); see the README.

usage: python3 rebuild_rule.py check B          every N < 2^B, both headers, n - len(N) + 1 in {0, 1}
       python3 rebuild_rule.py run R [SECONDS]   the first R rebuilds of the macro run from blank tape
       python3 rebuild_rule.py random T B        T random N of B digits, both headers
"""
import os, sys, time, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

M = "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB"
T = {"O": {0: "P", 1: "*", 2: "Q", 3: "O"},
     "P": {0: "P", 1: "P", 2: "*", 3: "Q"},
     "Q": {0: "R", 1: "P", 2: "P", 3: "Q"},
     "R": {0: "R", 1: "R", 2: "P", 3: "P"}}
START = {"0110101": "O", "0110111": "Q"}
HDR = {0: "0110101", 1: "0110111"}


def walk(N, H):
    """(j, b, path): digits read, the last digit, the automaton states; j = None if the walk reaches the top of N
    (the digits above the top count as 0, so then it stays in P or R for ever)"""
    s = START[H]; path = [s]; k = 0; L = N.bit_length()
    while 2 * k + 1 < L:
        s = T[s][(N >> (2 * k)) & 3]; k += 1
        if s == "*":
            j = 2 * k + 1
            return j, (N >> (j - 1)) & 1, path
        path.append(s)
    return None, None, path


def predict(H, n, N):
    j, b, _ = walk(N, H)
    if j is None or j >= N.bit_length() - 1: return None   # the walk reads every digit below the sentinel
    return (HDR[b], n + (5 * j + 1) // 2, N >> j)


def compare(rb, H, n, N):
    """'ok', 'top' (walk reaches the top of N: not covered by the rule), or a description of the mismatch"""
    p = predict(H, n, N)
    r = rb.rebuild(H, n, N, maxd=10 ** 9)
    if p is None:
        return "top", r
    if r[0] != "OK": return f"rule predicts {p} but rebuild gives {r[0]}", r
    H2, n2, N2, V2, f2, L2 = r[2]
    if (H2, n2, N2) != p: return f"rule predicts {p} but rebuild gives {(H2, n2, N2)}", r
    return "ok", r


def main():
    from rebuild import Rebuilder, macro_run
    rb = Rebuilder(M)
    cmd = sys.argv[1]
    if cmd == "check":
        B = int(sys.argv[2]); cnt = {"ok": 0, "top": 0}; bad = []
        for H in START:
            for N in range(2, 1 << B):
                for d in (0, 1):
                    n = N.bit_length() - 1 + d
                    if n < 1: continue
                    res, _ = compare(rb, H, n, N)
                    if res in cnt: cnt[res] += 1
                    else: bad.append((H, n, N, res))
        print(f"N < 2^{B}, both headers, n - len(N) + 1 in {{0, 1}}: {cnt['ok']} rebuilds follow the rule, "
              f"{cnt['top']} have a walk reaching the top of N (not covered), {len(bad)} contradict it")
        for x in bad[:20]: print("  ", x)
        sys.exit(1 if bad else 0)
    elif cmd == "random":
        Tn, B = int(sys.argv[2]), int(sys.argv[3]); random.seed(1); cnt = {"ok": 0, "top": 0}; bad = []; jmax = 0
        for t in range(Tn):
            N = (1 << (B - 1)) | random.getrandbits(B - 1)
            for H in START:
                res, r = compare(rb, H, N.bit_length() + random.randint(-1, 0), N)
                if res in cnt: cnt[res] += 1
                else: bad.append((H, N, res))
                if res == "ok": jmax = max(jmax, walk(N, H)[0])
        print(f"{Tn} random N of {B} digits, both headers: {cnt['ok']} follow the rule (longest walk j = {jmax}), "
              f"{cnt['top']} reach the top, {len(bad)} contradict it")
        for x in bad[:20]: print("  ", x)
        sys.exit(1 if bad else 0)
    elif cmd == "run":
        R = int(sys.argv[2]); secs = float(sys.argv[3]) if len(sys.argv) > 3 else 1e9
        st = {"prev": None, "ok": 0, "bad": [], "jmax": 0}

        def o(x):
            if x[0] == "start":
                st["prev"] = (x[1], x[2], x[3]); return
            if x[0] in ("HALT", "STUCK"):
                st["bad"].append(x); return
            it, H, n, N, form, steps, rs, subs, N2, d = x
            H0, n0, N0 = st["prev"]
            p = predict(H0, n0, N0)
            if p == (H, n, N2):
                st["ok"] += 1; st["jmax"] = max(st["jmax"], walk(N0, H0)[0])
            else:
                st["bad"].append((it, H0, n0, p, (H, n, N2)))
            st["prev"] = (H, n, N)
        macro_run(M, R, secs, o)
        print(f"macro run from blank tape: {st['ok']} rebuilds follow the rule (longest walk j = {st['jmax']}), "
              f"{len(st['bad'])} do not")
        for x in st["bad"][:10]: print("  ", str(x)[:300])
        sys.exit(1 if st["bad"] else 0)


if __name__ == "__main__":
    main()
