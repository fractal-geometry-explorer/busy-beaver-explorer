"""rsim_cmp MACHINE T1,T2,... [KEEP]: print what c/rsim.cpp prints in its 'dump' mode, from py/rsim.py, so the two
programs can be compared line for line (steps, state, jumps, rules applied, learn calls, samples, the whole tape)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.set_int_max_str_digits(0)
from rsim import RSim, Halt

def dump(sim):
    o = ''.join(f'{w}^{c} ' for w, c in sim.L) + '['
    for i, b in enumerate(sim.buf):
        if i == sim.h: o += '>'
        o += str(b)
    if sim.h >= len(sim.buf): o += '>'
    o += '] '
    if sim.h < 0: o += f'(h={sim.h}) '
    o += ''.join(f'{w}^{c} ' for w, c in reversed(sim.R))
    return o

if __name__ == '__main__':
    m = sys.argv[1]; ts = [int(float(t)) for t in sys.argv[2].split(',')]
    sim = RSim(m)
    if len(sys.argv) > 3: sim.KEEP = int(sys.argv[3])
    try:
        for t in ts:
            sim.run(t)
            print(f'T {t} steps {sim.steps} state {"ABCDEF"[sim.s]} jumps {sim.njumps} nrule {sim.nrule} nlearn {sim.nlearn} nsamp {sim.nsamp} tape {dump(sim)}', flush=True)
    except Halt:
        print('HALT', sim.steps)
