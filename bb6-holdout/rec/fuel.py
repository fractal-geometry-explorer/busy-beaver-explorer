"""For one cycle: at each round start during the longest right-end cascade, the marks as fractions of the tape,
and which cascade meetings happen in that round."""
import sys, tracecycle as T
def pred(d): return (d - 2) // 2 if d % 4 == 2 else d // 2 + 4
def run(n):
    meets = []; rnd = [0]
    def hook(ms, label, x):
        if label != "gap": return
        s = sorted(ms, key=lambda m: m[1]); r = [m for m in s if m[1] > x]
        if r and r[0][0] == "M" and r[0] is s[-1]: meets.append((rnd[0], r[0][1] - x - 3))
    T.HOOK = hook
    w = 2 * n + 6; marks = [["G", 1], ["M", w - 2]]; starts = []
    for i in range(400):
        rnd[0] = i; starts.append((w, sorted(([t, p] for t, p in marks), key=lambda m: m[1])))
        w, marks, ev = T.round_events(w, marks)
        if len(marks) == 2 and marks[1] == ["M", w - 2]: break
    best = []; cur = [meets[0]]
    for a, b in zip(meets, meets[1:]):
        cur = cur + [b] if b[1] == pred(a[1]) else [b]
        if len(cur) > len(best): best = list(cur)
    return starts, best
if __name__ == '__main__':
  n = int(sys.argv[1])
  starts, best = run(n)
  r0, r1 = best[0][0], best[-1][0]
  inchain = {}
  for r, d in best: inchain.setdefault(r, []).append(d)
  for i in range(r0 - 1, min(r1 + 3, len(starts))):
      w, ms = starts[i]
      desc = " ".join(f"{t}{p / w:.4f}" if p > 1 else f"{t}1" for t, p in ms)
      tag = ("meeting " + ", ".join(f"{'merge' if d % 4 == 2 else 'swap'}" for d in inchain[i])) if i in inchain else ""
      print(f"round {i:2d}  {desc:60s} {tag}")
