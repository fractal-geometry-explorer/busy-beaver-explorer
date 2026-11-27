"""The tail process on its own: take a real left-end list, keep its first P blocks, give each of them LIFE more rounds
of life (add LIFE*18*5^j to block j, which keeps its residue), drop the rest, and run R left-end events.
Report every new drift among the blocks after the prefix whose leading digits cancel (>= MINC digits).
usage: pure.py MACHINE BASE_EVENT P R OUT.json"""
import json
import os
import sys
PY = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..",
                  "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---", "py")
sys.path.insert(0, PY); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fast, frames
from b5 import b5
def nd5(x):
    x = abs(x); n = 0
    while x: x //= 5; n += 1
    return n
def main(machine, base_event, P, R, out, LIFE=10**6, MINC=5):
    fr, fa, st = frames.info(machine)
    h, r, s = fast.run(machine, 10 ** 150)
    base = list(h.top[base_event][2])
    assert len(base) > P + 1, len(base)
    L = [base[0]] + [base[1 + j] + LIFE * 18 * 5 ** j for j in range(P)]
    h2, o = fast.run_list(fa, L, 10 ** 100000, events=R)
    tops = [t[2] for t in h2.top]
    hist = {}; hits = []; prev = {}; tails = []
    for n, l in enumerate(tops):
        T = l[1:]; cur = {}
        for j in range(len(T) - 1):
            d = T[j + 1] - 5 * T[j]; cur[d] = cur.get(d, 0) + 1
            if prev.get(d, 0): prev[d] -= 1; continue
            if j < P - 1 or n == 0: continue
            c = max(nd5(5 * T[j]), nd5(T[j + 1])) - nd5(d)
            hist[c] = hist.get(c, 0) + 1
            if c >= MINC: hits.append({"round": n, "j": j, "k": len(T), "c": c, "d": str(d), "tj": b5(T[j]), "tj1": b5(T[j + 1])})
        prev = cur
        tails.append([b5(x) for x in T[P:]][-6:])
    json.dump({"machine": machine, "base_event": base_event, "P": P, "outcome": o, "rounds": len(tops), "k_end": len(tops[-1]) - 1,
               "prefix_ok": all(len(l) - 1 >= P for l in tops), "hist": hist, "hits": hits, "tails_first_60": tails[:60]}, open(out, "w"), indent=0)
    print(machine, base_event, o, "rounds", len(tops), "k_end", len(tops[-1]) - 1, "hist", sorted(hist.items()), "hits", [(x["round"], x["j"] - P, x["c"], x["d"][:30]) for x in hits][:40])
if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5])
