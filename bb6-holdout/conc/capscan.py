import subprocess, re, sys, collections
sys.path.insert(0, '.')
from entrydepth import entry_bits
src = sys.argv[1]; maxjobs = int(sys.argv[2]); extra = int(sys.argv[3])
lines = [l for l in open(src).read().split('\n') if l]
seen = set(); jobs = []
for l in lines:
    n = int(l.split()[0]); r0 = int(re.search(r'rounds (\d+)-', l).group(1)); ch = int(l.split()[2])
    s = entry_bits(n, r0); key = (n % (1 << s), s, r0)
    if key in seen: continue
    seen.add(key); jobs.append((n, r0, ch, s, ' '.join(l.split(':')[1].split()[:3])))
res = collections.Counter()
for n, r0, ch, s, tpl in jobs[:maxjobs]:
    out = subprocess.run(['python3', 'tree1d.py', str(n), str(s), str(r0), '60', str(s + extra)], capture_output=True, text=True, timeout=1800).stdout
    caps = [int(m.group(1)) for m in re.finditer(r'reaches\s+(\d+)\)', out)]
    lost = re.search(r'lost ([0-9.e+-]+)', out).group(1)
    mx = max(caps) if caps else 0
    res[(ch, mx)] += 1
    print(f"n = {n:16d} chain {ch:2d}, run from round {r0:3d}, entry digits {s:2d}, start [{tpl}]: largest run in entry class {mx}  (lost {lost})", flush=True)
print("(observed chain, largest in entry class):", sorted(res.items()))
