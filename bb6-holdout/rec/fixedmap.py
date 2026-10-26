import importlib, sys, json
import symjump as S
V = int(sys.argv[1])
res = {}
for v in range(0, V + 1):
    if v == 0:
        w0 = S.P(2, 2); w = w0; marks = [["G", S.P(0, 1)], ["M", w0 - 2]]
        for r in range(1, 50):
            w, marks = S.round_events(w, marks)
            if len(marks) == 2 and marks[1][0] == "M" and marks[1][1] == w - 2: res[0] = (int((w - w0).b) // 2, r); break
        continue
    j, r = S.jump(v)
    if j is not None: res[v] = (j, r)
json.dump(res, open(f"fixed_{V}.json", "w"))
print(len(res), "fixed classes up to", V)
