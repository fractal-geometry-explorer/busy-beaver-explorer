import sys, time
from z3 import *
from maps import M
name = sys.argv[1]; tmo = int(sys.argv[2])
n, start, rules = M[name]
fp = Fixedpoint(); fp.set(engine='spacer'); fp.set('timeout', tmo * 1000)
Inv = Function('Inv', *([IntSort()] * n + [BoolSort()])); fp.register_relation(Inv)
v = [Int('x%d' % i) for i in range(n)]
for x in v: fp.declare_var(x)
fp.rule(Inv(*[IntVal(s) for s in start]))
bad = []
for g, t in rules(v):
    if t == 'halt': bad.append(g)
    else: fp.rule(Inv(*t), [Inv(*v), g])
t0 = time.time()
try: r = fp.query(Exists(v, And(Inv(*v), Or(bad))))
except Z3Exception as e: r = 'exc ' + str(e)[:100]
print(name, r, '%.0fs' % (time.time() - t0), flush=True)
if r == unsat: print(fp.get_answer())
if r == sat: print('HALT REACHABLE?', fp.get_answer())
