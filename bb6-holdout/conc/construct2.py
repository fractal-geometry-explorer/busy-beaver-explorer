"""Explicit GMM states for an entry family found by entrycaps.py: route + p plain passes + entry + extra-wall word.
usage: construct2.py route_index p suffix_index word kmin kmax [max_found]"""
import sys, json
from fractions import Fraction as F
from conc import Model, Pos
import mixsolve as MS, routeexclude as RX
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from cyccost import CYC, outs as L_out
ri, p, si, word = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
kmin, kmax = int(sys.argv[5]), int(sys.argv[6]); maxf = int(sys.argv[7]) if len(sys.argv) > 7 else 3
r = [json.loads(l) for l in open('../routetree_routes30.txt')][ri]
sfx = [(a, b) for a, b, w in json.load(open('../entry_suffixes.json')) if a.count('GWWWW') == 1 and a[-1] == 'GWWWW'][si]
shapes = r['shapes'] + CYC * p + sfx[0] + sum(((MS.P_sh if x == 'P' else MS.Q_sh) for x in word), [])
outs = r['outs'] + L_out * p + sfx[1] + sum(((MS.P_out if x == 'P' else MS.Q_out) for x in word), [])
E_ex = 2 ** 40 + 1; m_ex = int(E_ex * r['ratio']) // 2 * 2
md, err = RX.forced(m_ex, E_ex, shapes, outs, 0, F(2) ** 200)
if md is None: print("geometry fails:", err); sys.exit()
C = RX.coset_of(md)
if C is None: print("coset inconsistent (the route's own digits conflict)"); sys.exit()
print(f"route {ri} + {p} passes + entry {si} + {word}: {len(shapes)} rounds, coset index 2^{C.index_bits():.1f}")
found = 0; tried = 0
for k in range(kmin, kmax + 1):
    for m, E in RX.points(C, k):
        tried += 1
        mm = Model(0); mm.W = mm.const(E); mm.add('G', mm.const(1)); mm.add('M', mm.const(m)); mm.add('M', mm.W - 2)
        sh = []
        for rr in range(len(shapes) + 10):
            mm.do_round()
            if mm.halted or mm.bad: break
            sh.append(mm.shape())
        if sh[:len(shapes)] == shapes:
            found += 1
            print(f"  width 2^{k}: m = {m}, E = {E} follows it; then {' '.join(sh[len(shapes):len(shapes) + 10])}", flush=True)
            if found >= maxf: break
        if tried > 2000000: break
    if found >= maxf or tried > 2000000: break
print(f"tried {tried}, found {found}")
