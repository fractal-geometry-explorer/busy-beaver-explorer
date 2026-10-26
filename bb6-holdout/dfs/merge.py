"""Merge nrefdfs part outputs; optionally compare per-level lines with the disk engine's log.
usage: merge.py out_part0 out_part1 ... [--cmp nd_run.log]"""
import re, sys
args = sys.argv[1:]; cmpf = None
if '--cmp' in args: i = args.index('--cmp'); cmpf = args[i + 1]; args = args[:i] + args[i + 2:]
pat = re.compile(r'digits +(\d+): settled (\d+), still open (\d+), longest chain here (\d+) \(overall \d+\), largest j_min (\d+), direct runs (\d+) \(problems (\d+), longest chain (\d+) at n = (\d+)\), class problems (\d+)')
L = {}; MS = {}; tot = dict(J=0, Jn=0); special = []
for f in args:
    for l in open(f):
        m = pat.match(l)
        if m:
            k = int(m.group(1)); v = list(map(int, m.groups()[1:]))
            a = L.setdefault(k, [0, 0, 0, 0, 0, 0, 0, 0, 0])
            a[0] += v[0]; a[1] += v[1]; a[2] = max(a[2], v[2]); a[3] = max(a[3], v[3]); a[4] += v[4]; a[5] += v[5]
            if v[6] > a[6] or (v[6] == a[6] and v[6] > 0 and v[7] < a[7]): a[6], a[7] = v[6], v[7]
            a[8] += v[8]; continue
        m = re.match(r'  (\w+) (\w\w) min (-?\d+) \(n=(\d+)\)', l)
        if m:
            key = (m.group(1), m.group(2)); val = (int(m.group(3)), int(m.group(4)))
            if key not in MS or val < MS[key]: MS[key] = val
            continue
        m = re.match(r'totals: .*largest jump (\d+) \(n = (\d+)\)', l)
        if m:
            J, n = int(m.group(1)), int(m.group(2))
            if J > tot['J']: tot['J'], tot['Jn'] = J, n
            continue
        if 'HALTS' in l or 'bad' in l or 'too long' in l or l.startswith('  chain'): special.append(l.rstrip())
ov = 0; ts = td = tp = 0
for k in sorted(L):
    a = L[k]; ov = max(ov, a[2]); ts += a[0]; td += a[4]; tp += a[5] + a[8]
    print(f"digits {k:2d}: settled {a[0]}, still open {a[1]}, longest chain here {a[2]} (overall {ov}), largest j_min {a[3]}, direct runs {a[4]} (problems {a[5]}, longest chain {a[6]} at n = {a[7]}), class problems {a[8]}")
print("closest approaches (lower bounds):")
for key in sorted(MS, key=lambda t: (['gap', 'shift', 'packet'].index(t[0]), ['GMWB'.index(c) for c in t[1]])):
    print(f"  {key[0]} {key[1]} min {MS[key][0]} (n={MS[key][1]})")
print(f"totals: settled classes {ts}, direct runs {td}, problems {tp}, largest jump {tot['J']} (n = {tot['Jn']}), longest chain {ov}")
print(f"special lines: {len(special)}"); [print(s) for s in special if 'chain' not in s]
if cmpf:
    R = {}
    for l in open(cmpf):
        m = pat.match(l)
        if m: R[int(m.group(1))] = list(map(int, m.groups()[1:]))
    nd = 0; bad = []
    for k in sorted(L):
        if k in R:
            nd += 1; a, b = L[k], R[k]
            if a[:7] != b[:7] or a[8] != b[8]: bad.append(k)
            elif a[7] != b[7]: print(f"level {k}: same longest direct chain {a[6]}, first n differs ({a[7]} vs {b[7]})")
    print(f"compared {nd} levels with {cmpf}: mismatches {bad}")
