"""The two-round feeding loop, checked on every residue class.
Start: round-start state G1, W a, W b, width w (nothing else). Let d = w - b - 3 (the distance at the end-marker
meeting two rounds later). For each class of (b mod 2^K, d mod 2^K), two independent huge lifts are run in the mark
model; the outcome must not depend on the lift. Reported: what the next two rounds do, and how long the cascade
(meetings following the halving rule) lasts from this state."""
import sys, random, collections
import tracecycle as T

def pred(d): return (d - 2) // 2 if d % 4 == 2 else d // 2 + 4

def run(b, d, max_rounds=400):
    w = b + d + 3; a = 5 + (b // 7) * 2
    marks = [["G", 1], ["W", a], ["W", b]]
    meets = []
    def hook(ms, label, x):
        if label != "gap": return
        s = sorted(ms, key=lambda m: m[1]); r = [m for m in s if m[1] > x]
        if r and r[0][0] == "M" and r[0] is s[-1]: meets.append(r[0][1] - x - 3)
    T.HOOK = hook
    shapes = []
    for rnd in range(max_rounds):
        w, marks, ev = T.round_events(w, marks)
        shapes.append(tuple(m[0] for m in sorted(marks, key=lambda m: m[1])))
        if len(marks) == 2 and marks[1] == ["M", w - 2]: break
        if len(meets) >= 2 and meets[-1] != pred(meets[-2]): break
    L = 1
    for x, y in zip(meets, meets[1:]):
        if y == pred(x): L += 1
        else: break
    return (meets[0] if meets else None), L, shapes[1] if len(shapes) > 1 else None, meets

K = int(sys.argv[1]); M = 1 << K
random.seed(1)
lens = collections.Counter(); undetermined = 0; firstd_ok = True
two_round = collections.Counter()
for b0 in range(0, M, 2):                 # the right wall sits at an even cell
    for d0 in range(0, M, 2):                 # d is always even
        res = []
        for lift in range(2):
            X = random.getrandbits(44) | (1 << 44); Y = random.getrandbits(44) | (1 << 45)
            b = b0 + M * X; d = d0 + M * Y
            if b % 2 == 0 and b < 8: continue
            fd, L, shape2, meets = run(b, d)
            res.append((L, shape2, fd == d))
        if len(res) < 2: continue
        firstd_ok &= res[0][2] and res[1][2]
        if res[0][:2] != res[1][:2]: undetermined += 1; continue
        lens[res[0][0]] += 1
        two_round[(b0 % 4, d0 % 8, res[0][1])] += 1
print(f"K = {K}: classes of (b mod {M}, d mod {M}) with d even")
print("first meeting has d = w - b - 3 in every run:", firstd_ok)
print("cascade length from the loop state (meetings):", dict(sorted(lens.items())), " classes whose outcome depends on higher bits:", undetermined)
print("state after two rounds, by b mod 4 and d mod 8:")
for (bm, dm, sh), c in sorted(two_round.items()):
    print(f"   b≡{bm} (mod 4), d≡{dm} (mod 8): {' '.join(sh) if sh else '-'}  ({c} classes)")
