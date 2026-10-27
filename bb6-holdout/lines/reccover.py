"""Do the record runs enter the loop through listed prefixes?  For each record n: the GMM state that starts the
segment holding its closest meeting (from lined SEGOUT), then the shapes and outcomes from it to each G W W W, looked
up among the 759,918 prefixes of the 46-bit tree.  usage: reccover.py n ..."""
import sys, json, subprocess
sys.path.insert(0, '../conc')
from conc import Model
D = '../'
routes = {}
for l in open(D + 'rtree46_W.jsonl'):
    r = json.loads(l); routes[(tuple(r['shapes']), tuple(r['outs']))] = r['measure']
print(len(routes), 'prefixes loaded')
for n in sys.argv[1:]:
    out = subprocess.run([D + 'csearch/lined_tr', 'n'], input=n + '\n', capture_output=True, text=True, env={'SEGOUT': '1'}).stdout
    m, E = [int(x) for x in out.split('SEG ')[1].split()[:2]]
    md = Model(0); md.W = md.const(E); md.add('G', md.const(1)); md.add('M', md.const(m)); md.add('M', md.W - 2)
    shapes = []; found = []
    for r in range(60):
        md.do_round(); shapes.append(md.shape()); outs = tuple(md.outcomes)
        if shapes[-1] == 'GWWW':
            key = (tuple(shapes), outs)
            found.append((r + 1, key in routes, routes.get(key)))
        if shapes[-1] == 'GM': break
        if shapes[-1] == 'GMM' and md.marks()[-1][1] == md.W - 2 and r > 0: break
    print(f'n = {n}: segment from m = {m}, E = {E} (m/E = {m / E:.5f}); G W W W at rounds', found)
