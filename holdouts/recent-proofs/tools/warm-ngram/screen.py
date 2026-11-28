# Warm-start n-gram CTL screen (busycoq PR #121 technique) over the open holdouts, one shard.
# usage: python3 screen.py SHARD NSHARDS
import sys, subprocess, json, time, longrun
shard, nsh = int(sys.argv[1]), int(sys.argv[2])
machines = [m.strip() for m in open('open501.txt') if m.strip()][shard::nsh]
GRID = [(simT, n, h) for simT in (10000, 100000, 1000000) for n in (2, 3, 4, 6, 8)
        for h in ((12, 2), (8, 4), (6, 8), (1, 12), (0, 6), (4, 0))]
st = longrun.load(default={"done": {}, "nonhalt": []})
last = time.time()
for m in machines:
    if m in st["done"]:
        continue
    res = []
    for simT, n, (l1, l2) in GRID:
        try:
            out = subprocess.run(['./wng', m, str(simT), str(n), str(l1), str(l2), '0', '-C', '1000000'],
                                 capture_output=True, text=True, timeout=20).stdout.split()
        except subprocess.TimeoutExpired:
            out = ['TIMEOUT']
        r = out[0] if out else 'ERROR'
        res.append([simT, n, l1, l2, r] + out[1:2])
        if r in ('NONHALT', 'HALT'):
            st["nonhalt"].append([m, simT, n, l1, l2, r])
    st["done"][m] = res
    if time.time() - last > 120:
        longrun.save(st, progress="machines %d/%d nonhalt=%d" % (len(st["done"]), len(machines), len(st["nonhalt"])))
        last = time.time()
longrun.save(st, progress="DONE machines %d nonhalt=%d" % (len(st["done"]), len(st["nonhalt"])))
