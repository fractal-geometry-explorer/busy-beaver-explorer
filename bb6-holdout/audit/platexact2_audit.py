"""Exact in-run exits from every plateau limit (gx3 plat, GXENTRIES=1, to CAP digits), each entry classified by whether
its route uses a round of the extra-wall loop.  Writes one line per entry.  usage: platexact2.py CAP > out"""
import json, subprocess, re, os, sys
os.environ['GXENTRIES'] = '1'; CAP = sys.argv[1]
d = json.load(open('runs/patinst.json'))
XW = {'GBWW', 'GWWWW', 'GMBW', 'GMWWW', 'GMMWW'}
npat = ncut = 0
for key, (Ws, marks, fstar) in d.items():
    if fstar is None: continue
    W0 = int(Ws); ms0 = [(t, int(p)) for t, p in marks]
    endm = ms0[-1][0] == 'M' and ms0[-1][1] == W0 - 2
    inner = fstar[:len(fstar) - (1 if endm else 0)]
    if inner and max(inner) > 1 - 1e-9: continue
    types = ''.join(t for t, p in ms0[1:]); nfree = len(types) - (1 if endm else 0)
    out = subprocess.run(['audit/gx3_audit', 'plat', types, '1' if endm else '0', '2', CAP] + [str(x) for x in fstar[:nfree]], capture_output=True, text=True); sys.stderr.write(out.stderr.split('AUDIT')[-1] if 'AUDIT' in out.stderr else ''); out = out.stdout
    cut = int(re.search(r'cut (\d+);', out).group(1)); npat += 1; ncut += cut > 0
    for line in out.splitlines():
        if line.startswith('E '):
            m = re.match(r'E sigma (\S+) s (\S+) lambda (\S+) bits (\d+) m (\d+) \| (.*)', line)
            route = m.group(6).split(); nxw = sum(1 for r in route if r in XW)
            print('pattern %s | sigma %s s %s lambda %s bits %s passes %s xwrounds %d | %s' % (key, m.group(1), m.group(2), m.group(3), m.group(4), m.group(5), nxw, ' '.join(route)))
print('# patterns %d, with cuts at %s digits: %d' % (npat, CAP, ncut), file=sys.stderr)
