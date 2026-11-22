"""Run chainsim on every machine of a list with several block sizes; one JSON line per machine.
usage: python3 chain_batch.py names.txt SECONDS_PER_K > out.jsonl"""
import sys, json
from chainsim import run
names = [l.split()[0] for l in open(sys.argv[1]) if l.strip()]
sec = float(sys.argv[2])
for n in names:
    res = {}
    for k in (1, 2, 3, 4, 6):
        r = run(n, k, 10**12, sec)
        res[k] = [str(x) if isinstance(x, int) and x > 10**15 else x for x in r]
        if r[0] == "halt": break
    best = max(res.items(), key=lambda kv: int(kv[1][1]))
    print(json.dumps({"machine": n, "by_k": res, "max_steps_digits": len(str(best[1][1]))}), flush=True)
