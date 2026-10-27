"""Exact exits from every plateau pattern's limit geometry: run gx3 plat for each (all branches to CAP digits) and
collect the largest sigma of a plain-loop entry with 0, 1, 2 extra-wall passes.  usage: platexact.py CAP MMAX"""
import json, subprocess, sys, re
CAP = sys.argv[1]; MMAX = sys.argv[2]
d = json.load(open('runs/patinst.json'))
rows = []
for key, (Ws, marks, fstar) in d.items():
    if fstar is None: continue
    W0 = int(Ws); ms0 = [(t, int(p)) for t, p in marks]
    endm = ms0[-1][0] == 'M' and ms0[-1][1] == W0 - 2
    inner = fstar[:len(fstar) - (1 if endm else 0)]
    if inner and max(inner) > 1 - 1e-9: continue
    types = ''.join(t for t, p in ms0[1:])
    nfree = len(types) - (1 if endm else 0)
    fr = [str(x) for x in fstar[:nfree]]
    cmd = ['csearch/gx3', 'plat', types, '1' if endm else '0', MMAX, CAP] + fr
    out = subprocess.run(cmd, capture_output=True, text=True).stdout
    sig = {}
    for m in re.finditer(r'after (\d+) extra-wall passes: entry measure (\S+), largest sigma ([0-9.]+)', out):
        sig[int(m.group(1))] = (float(m.group(2)), float(m.group(3)))
    head = out.splitlines()[0] if out else 'no output'
    rows.append((key, types, endm, sig, head))
    print(key, '|', types, 'endm' if endm else '', '|', ' '.join('m%d: meas %.3g sig %.2f' % (m, v[0], v[1]) for m, v in sorted(sig.items())), '|', head[:160], flush=True)
best = {}
for key, types, endm, sig, head in rows:
    for m, (meas, sg) in sig.items():
        if sg > best.get(m, (-1, ''))[0]: best[m] = (sg, key)
print('LARGEST:', best)
