import subprocess, re, sys, collections
sys.path.insert(0, '.')
from entrydepth import entry_bits
from concurrent.futures import ThreadPoolExecutor
src = sys.argv[1]; maxjobs = int(sys.argv[2]); extra = int(sys.argv[3])
jobs = []; seen = set()
for l in open(src):
    if not l.strip(): continue
    n, r0, L = map(int, l.split())
    s = entry_bits(n, r0); key = (n % (1 << s), s, r0)
    if key in seen: continue
    seen.add(key); jobs.append((n, r0, L, s))
    if len(jobs) >= maxjobs: break
def work(j):
    n, r0, L, s = j
    out = subprocess.run(['python3', 'tree1d.py', str(n), str(s), str(r0), '60', str(s + extra)], capture_output=True, text=True, timeout=3600).stdout
    caps = [int(m.group(1)) for m in re.finditer(r'reaches\s+(\d+)\)', out)]
    probs = {int(a): float(b) for a, b in re.findall(r'reaches\s+(\d+)\) = ([0-9.e+-]+)', out)}
    return n, r0, L, s, (max(caps) if caps else 0), probs, re.search(r'lost ([0-9.e+-]+)', out).group(1)
res = collections.Counter(); allp = collections.defaultdict(float)
with ThreadPoolExecutor(8) as ex:
    for n, r0, L, s, mx, probs, lost in ex.map(work, jobs):
        res[mx] += 1
        for k, v in probs.items(): allp[k] += v
        print(f"n = {n} run from round {r0} (length {L}), entry digits {s}: cap {mx}, lost {lost}", flush=True)
print("caps:", sorted(res.items()))
tot = len(jobs)
print("average over entry classes of P(run >= L | entry):", ' '.join(f"{k}:{allp[k]/tot:.3g}" for k in sorted(allp)))
