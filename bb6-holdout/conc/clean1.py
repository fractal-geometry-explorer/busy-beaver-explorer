import sys
from conc import *
from fractions import Fraction as F
def run(n, verbose=True):
    m = Model(1); m.W = m.var(0, 2 * n + 6); m.add('G', m.const(1)); m.add('M', m.var(0, 2 * n + 4))
    nc = 0; ne = 0; rd = 0
    while True:
        m.do_round(); rd += 1
        if m.halted or m.bad: print("halt/bad"); return
        mk = m.marks()
        path = ' '.join(m.path); m.path = []
        if verbose:
            tests = []
            for d, res, mod in m.cong[nc:]:
                tests.append(f"[{fmt(d, ['N'])}]={res}")
            ends = [f"END d={fmt(d, ['N'])}" for (r_, d) in m.endd[ne:]]
            print(f"rd {rd:3d} {m.shape():10s} {' '.join(ends)}  tests: {' '.join(tests)}")
        nc = len(m.cong); ne = len(m.endd)
        if len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == m.W.v - 2: break
    print("next n form:", fmt((m.W - 6).half(), ['N']), " rounds", rd)
    return m
run(int(sys.argv[1]))
