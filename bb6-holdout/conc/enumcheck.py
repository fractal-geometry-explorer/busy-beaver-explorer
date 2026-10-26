"""End-to-end check of the route exclusion's candidate enumeration: random GMM states at width 2^k that follow the
main route (route 0 of the 30-bit list, shapes and outcomes) and then complete at least the required number of plain
passes must all appear in the candidate file."""
import json, random, math, sys
from fractions import Fraction as F
from conc import Model
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from cyccost import CYC, outs as L_out
k = int(sys.argv[1]); N = int(sys.argv[2]); S = 12
cands = set()
for l in open('../rt30s_cands.txt'):
    m, E = l.split()
    E = int(E)
    if 2 ** k <= E < 2 ** (k + 1): cands.add((int(m), E))
r0 = json.loads(open('../routetree_routes30.txt').readline())
H = 2.0   # route 0's H (rt30s_summary)
preq = max(1, math.ceil((k - S - H) / 4))
want = r0['shapes'] + CYC * preq; wout = r0['outs'] + L_out * preq
random.seed(k)
hit = miss = follow = 0
for it in range(N):
    E = random.randrange(2 ** k, 2 ** (k + 1)) | 1; m = random.randrange(4, E - 7) & ~1
    md = Model(0); md.W = md.const(E); md.add('G', md.const(1)); md.add('M', md.const(m)); md.add('M', md.W - 2)
    ok = True
    for i, sh in enumerate(want):
        md.do_round()
        if md.halted or md.bad or md.shape() != sh: ok = False; break
        if md.outcomes != wout[:len(md.outcomes)]: ok = False; break
    if not ok or md.outcomes[:len(wout)] != wout: continue
    follow += 1
    if (m, E) in cands: hit += 1
    else: miss += 1; print("MISSING", m, E)
print(f"k = {k}: {len(cands)} candidates in range; sampled {N}; {follow} follow route 0 + {preq} passes; in list {hit}, missing {miss}")
