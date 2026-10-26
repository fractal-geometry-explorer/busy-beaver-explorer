"""Explicit GMM states that run a GMM-born chain: route + plain passes + entry + extra-wall word + drop + q plain
passes; for each q, the first coset points by width, run concretely, closest approach reported.
usage: chainconstruct.py chain_index qmax kmax"""
import sys, json, math
from fractions import Fraction as F
from conc import Model
import routeexclude as RX
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from cyccost import CYC, outs as L_out
ci, qmax, kmax = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
r = [json.loads(l) for l in open('../chain_routes.jsonl')][ci]
E_ex = 2 ** 40 + 1; m_ex = int(E_ex * r['ratio']) // 2 * 2
def closest(m, E, nr):
    md = Model(0); md.W = md.const(E); md.add('G', md.const(1)); md.add('M', md.const(m)); md.add('M', md.W - 2)
    ends = []; sh = []
    for k in range(nr):
        ne = len(md.endd); md.do_round()
        if md.halted or md.bad: return sh, None, 'halted' if md.halted else 'bad'
        sh.append(md.shape()); ends += [d.v for rr, d in md.endd[ne:]]
    return sh, math.log2(E / min(ends)), ''
for q in range(0, qmax + 1):
    md, err = RX.forced(m_ex, E_ex, r['shapes'], r['outs'], q, F(2) ** (4 * q + 220))
    if md is None: print(q, 'geometry', err); continue
    C = RX.coset_of(md)
    if C is None: print(q, 'inconsistent'); continue
    want = r['shapes'] + CYC * q
    best = None
    for k in range(17, kmax + 1):
        n = 0
        for m, E in RX.points(C, k):
            n += 1
            sh, h, st = closest(m, E, len(want) + 12)
            if sh[:len(want)] == want:
                best = (k, m, E, h, st); break
            if n > 50: break
        if best: break
    print(f"q = {q}: coset 2^{C.index_bits():.0f}; first state following it: {best}", flush=True)
