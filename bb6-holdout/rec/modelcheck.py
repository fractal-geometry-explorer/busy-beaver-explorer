import json, sys, time
from clean_recurrence import next_clean
rows = [json.loads(l) for l in open("longrun.log")]
targets = {r["cleans"]: r["last_clean"][1] for r in rows}
n, count, t0, ok = 2, 1, time.time(), True
while count < max(targets):
    n, _ = next_clean(n); count += 1
    if count in targets:
        print(count, "clean tapes: model n =", n, " certified n =", targets[count], n == targets[count], flush=True)
        ok &= n == targets[count]
print("model agrees at every checkpoint:", ok, round(time.time() - t0), "s")
