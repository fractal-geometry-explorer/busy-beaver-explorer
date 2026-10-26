"""Classify what happens between consecutive steps of the right-end cascade (mark model).
A cascade step is a meeting between a gap and the end marker; consecutive meetings belong to one chain when
d_next = (d - 2)/2 after a merge or d/2 + 4 after a swap."""
import sys, re, collections, json
import tracecycle as T

def pred(d): return (d - 2) // 2 if d % 4 == 2 else d // 2 + 4
def kind(e):
    e = re.sub(r"[0-9]+", "#", e)
    e = e.replace("G#/M#", "").replace(" d=#", "").replace("→W#", "")
    return e.strip()

def analyse(n):
    meet = []          # (global event index, d)
    allev = []
    rstarts = []
    def hook(marks, label, x):
        if label != "gap": return
        ms = sorted(marks, key=lambda m: m[1]); r = [m for m in ms if m[1] > x]
        if r and r[0][0] == "M" and r[0] is ms[-1]:
            meet.append((base[0] + len(T.CURRENT_EV), r[0][1] - x - 3))
    base = [0]
    orig = T.round_events
    def rr(w, marks):
        out = orig(w, marks)
        return out
    T.HOOK = hook
    w = 2 * n + 6; marks = [["G", 1], ["M", w - 2]]
    for rnd in range(5000):
        base[0] = len(allev)
        w, marks, ev = T.round_events(w, marks)
        allev.extend(ev); allev.append("|")       # | = new round (packet reached the left end)
        if len(marks) == 2 and marks[1] == ["M", w - 2]: break
    # chains
    chains = []; cur = [meet[0]] if meet else []
    for a, b in zip(meet, meet[1:]):
        if b[1] == pred(a[1]): cur.append(b)
        else:
            chains.append(cur); cur = [b]
    if cur: chains.append(cur)
    best = max(chains, key=len)
    steps = []
    for a, b in zip(best, best[1:]):
        seg = allev[a[0]:b[0]]
        word = " ; ".join(kind(e) for e in seg)
        steps.append(("merge" if a[1] % 4 == 2 else "swap", word))
    return best, steps

if __name__ == "__main__":
    ns = [int(x) for x in sys.argv[1:]]
    words = collections.Counter(); trans = collections.Counter()
    for n in ns:
        best, steps = analyse(n)
        print(f"n = {n}: chain of {len(best)} meetings, d from {best[0][1]} to {best[-1][1]}")
        prev = None
        for t, wd in steps:
            words[(t, wd)] += 1
    print()
    for (t, wd), c in words.most_common():
        print(f"{c:3d}  after a {t}:  {wd[:300]}")
