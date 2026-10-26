"""Many more GMM-born entry families into G W W W W: every 30-bit route into the plain loop, then p plain passes,
then one of the observed ways from G W W W into G W W W W.  For each family (2-parameter position map) compute the
P/Q words it allows (bare family: only m even, E odd), and report families allowing two or more passes.
usage: entrycaps.py pmax [max_routes]"""
import sys, json, copy, collections
from fractions import Fraction as F
from conc import Model, Pos
from ewlock2 import consistent
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from cyccost import CYC, outs as L_out
pmax = int(sys.argv[1]); maxr = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 9
routes = [json.loads(l) for l in open('../routetree_routes30.txt')][:maxr]
sfx = [(a, b) for a, b, w in json.load(open('../entry_suffixes.json')) if a.count('GWWWW') == 1 and a[-1] == 'GWWWW']
def start(r):
    E_ex = 2 ** 40 + 1; m_ex = int(E_ex * r['ratio']) // 2 * 2; sc = F(2) ** 200
    md = Model(2); md.W = Pos([F(0), F(1), F(0)], F(E_ex) * sc)
    md.add('G', md.const(1)); md.add('M', Pos([F(1), F(0), F(0)], F(m_ex) * sc)); md.add('M', md.W - 2)
    return md
def run(md, shapes, outs):
    md.force = list(outs)
    for want in shapes:
        md.do_round()
        if md.bad or md.halted or md.shape() != want: return False
    return not md.force
def words_allowed(md):
    mk = md.marks(); fam = [list(q.f) for t, q in mk[1:]] + [list(md.W.f)]
    fam2 = [[f[0] * 2, f[1] * 2, f[2] + f[1]] for f in fam]      # m = 2u, E = 2v + 1
    frontier = ['']; longest = 0; allw = []
    for L in range(1, 4):
        nxt = [w + x for w in frontier for x in 'PQ' if consistent(fam2, 2, w + x)]
        if not nxt: break
        longest = L; frontier = nxt; allw = nxt
    return longest, allw
tally = collections.Counter(); found = []
for ri, r in enumerate(routes):
    base = start(r)
    if not run(base, r['shapes'], r['outs']): continue
    for p in range(pmax + 1):
        if p:
            if not run(base, CYC, L_out): break
        for si, (a, b) in enumerate(sfx):
            md = copy.deepcopy(base)
            if not run(md, a, b): continue
            longest, allw = words_allowed(md)
            tally[longest] += 1
            if longest >= 2:
                found.append((ri, p, si, allw)); print(f"route {ri} + {p} passes + entry {si}: words {allw}", flush=True)
    if ri % 200 == 0: print(f"... {ri} routes, families by cap {dict(tally)}", flush=True)
print("families by longest allowed word:", dict(tally))
json.dump(found, open(f'../entrycaps_found_p{pmax}.json', 'w'))
