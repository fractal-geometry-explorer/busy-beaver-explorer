"""Round-by-round comparison of the real machine (hybrid simulator) with the mark model, from a marks file."""
import sys
sys.path.insert(0, '../conc')
import hybsim, casesim, proofs
from hybsim import config_from, gap_phase, packet_phase, Uncovered
from conc import Model
xs = list(map(int, open(sys.argv[1]).read().split())); walls, Wd = xs[:-1], xs[-1]
NR = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 9
cfg = config_from([('G', 1)] + [('W', p) for p in walls], Wd)
mm = Model(1); mm.W = mm.const(Wd); mm.add('G', mm.const(1))
for v in walls: mm.add('W', mm.const(v))
def model_marks(m):
    return m.W.v, [(t, p.v) for t, p in m.marks()]
phase = 'gap'; rd = 0
def short(w, mk):
    return [(t, p if p < 10**4 else f"E-{w - p}") for t, p in mk]
while rd < NR:
    try:
        if phase == 'gap':
            cfg = gap_phase(cfg); phase = 'gap' if proofs.is_pass_position(cfg) else 'packet'; continue
        cfg, kind = packet_phase(cfg)
        if kind is None: phase = 'gap'; continue
        if kind == 'packet': continue
    except Uncovered as e:
        print(f"round {rd + 1}: real machine leaves the rules: {str(e)[:120]}"); break
    rd += 1; phase = 'gap'
    w, mk = casesim.marks_of(cfg)
    mm.do_round(); mw, mmk = model_marks(mm)
    same = (w == mw and mk == mmk)
    if not same or rd % 1 == 0 and NR < 10 ** 9:
        print(rd, "same" if same else "DIFF", "real:", w, short(w, mk), " model:", mw, short(mw, mmk))
    if not same: break
