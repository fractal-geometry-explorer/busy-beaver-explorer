import json, sys
import symjump as S, universal as U, ruleb as B
res = {int(k): v for k, v in json.load(open("fixed_260.json")).items()}
# limit process: virtual clean rounds and the precision each round needs
prec = {}; cur = [0]; base = U.mod4_U
def rec(d): cur[0] = max(cur[0], d.a.denominator.bit_length() - 1); return base(d)
S.mod4 = rec
w = S.P(2, 2); marks = [["G", S.P(0, 1)], ["M", w - 2]]; sing = {0: -2}
for r in range(1, 262):
    cur[0] = 0; w, marks = S.round_events(w, marks); prec[r] = cur[0]
    if len(marks) == 3 and marks[2][0] == "M" and marks[2][1].a == 2: sing[r] = (int(marks[2][1].b) - 3) // 2
S.mod4 = base
Ps = {}; m = 0
for r in range(1, 262): m = max(m, prec[r]); Ps[r] = m
Rs = sorted(sing)
agree = disagree = skipped = 0; notes = []
for v in range(1, 261):
    R = max(x for x in Rs if x <= v); k = v - R; t = sing[R]
    if R > 0 and Ps[R] > v - 2: skipped += 1; notes.append(f"v={v}: left the limit process before round {R}"); continue
    out = B.run(k, 40, t % 2 ** 40)
    pred = (int(out[1][0] * t + out[1][1])) if out[0] == "fixed" else None
    if out[0] == "fixed" and out[3] + 2 > v: notes.append(f"v={v}: needs R larger (alpha den 2^{out[3]})")
    actual = res.get(v, [None])[0]
    if pred == actual: agree += 1
    else: disagree += 1; notes.append(f"v={v}: R={R} k={k} n*={t}: predicted {pred}, actual {actual} ({out[0]})")
print(f"v = 1..260: agree {agree}, disagree {disagree}, outside the starting condition {skipped}")
for s in notes: print("  " + s)
