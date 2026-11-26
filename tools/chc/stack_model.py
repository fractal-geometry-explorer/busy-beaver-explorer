"""CHC encoding of the integer counter-stack model (py/stackmodel.py, lean/Model.lean mstepN) of
1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC.  Stack top = head of list."""
import sys, z3
from z3 import *
mode = sys.argv[1]; tmo = int(sys.argv[2])
I = IntSort(); B = BoolSort()
L = Datatype('L'); L.declare('nil'); L.declare('cons', ('k', I), ('cl', B), ('tl', L)); L = L.create()
nil, cons = L.nil, L.cons
Step = Function('Step', L, I, L, I, I, B)
Fail = Function('Fail', L, I, B)
Inv = Function('Inv', L, I, B)
Pile = Function('Pile', L, B)      # only K'(0)
Good = Function('Good', L, B)      # every K(0) directly on the pile
fp = Fixedpoint(); fp.set(engine='spacer'); fp.set('timeout', tmo*1000)
for f in (Step, Fail, Inv, Pile, Good): fp.register_relation(f)
k, s, r1, r2, k2, N, N2, o, j = Ints('k s r1 r2 k2 N N2 o j')
V, V2, W, W2 = Consts('V V2 W W2', L)
c = Bool('c')
vs = [k, s, r1, r2, k2, N, N2, o, j, V, V2, W, W2, c]
def rule(head, body=None):
    fp.rule(ForAll(vs, Implies(body, head)) if body is not None else head)
rule(Step(nil, 0, nil, 2, 2))
rule(Step(nil, 1, cons(0, False, nil), 0, 0))
rule(Step(cons(k, False, V), 0, cons(k, True, V), 2, 2), k >= 0)
rule(Step(cons(k, False, V), 1, cons(k2, False, V2), k - k2 + r2, k - k2 + r2),
     And(k >= 0, Step(V, k % 2, V2, r1, r2), k2 == (3 * k) / 2 + r1, k2 >= 0))
rule(Step(cons(0, True, V), 1, cons(0, False, cons(0, True, V)), 0, 0), True)
rule(Step(cons(k, True, V), s, V2, r1 + (3 * k) / 2 + 2 + s * (1 + k % 2), r2 + k + 2),
     And(k >= 0, Or(s == 0, s == 1), Not(And(k == 0, s == 1)), Step(V, (k + s) % 2, V2, r1, r2)))
rule(Fail(cons(k, False, V), 1), And(k >= 0, Step(V, k % 2, V2, r1, r2), (3 * k) / 2 + r1 < 0))
rule(Fail(cons(k, False, V), 1), And(k >= 0, Fail(V, k % 2)))
rule(Fail(cons(k, True, V), s), And(k >= 0, Or(s == 0, s == 1), Not(And(k == 0, s == 1)), Fail(V, (k + s) % 2)))
rule(Pile(nil)); rule(Pile(cons(0, True, V)), Pile(V))
rule(Good(nil)); rule(Good(cons(0, False, V)), Pile(V))
rule(Good(cons(k, c, V)), And(Good(V), Or(c, k > 0)))
rule(Good(cons(0, True, V)), Good(V))
if mode == 'orbit':
    rule(Inv(cons(2, False, nil), 48))
    rule(Inv(W2, N2), And(Inv(W, N), Step(W, N % 2, W2, o, r2),
         N2 == If(N % 2 == 0, (3 * N) / 2 + 5, (3 * N + 9) / 2) + o))
    bad = [Exists([W, N], And(Inv(W, N), Fail(W, N % 2))), Exists([W, N], And(Inv(W, N), N < 5))]
else:   # free parities: closed set of walls from the wall 1
    rule(Inv(nil, 0))
    rule(Inv(W2, 0), And(Inv(W, 0), Or(s == 0, s == 1), Step(W, s, W2, o, r2)))
    bad = [Exists([W, s], And(Inv(W, 0), Or(s == 0, s == 1), Fail(W, s)))]
for q in bad:
    try: r = fp.query(q)
    except z3.Z3Exception as e: r = 'exception ' + str(e)[:200]
    print(mode, 'query ->', r, fp.get_reason_unknown() if str(r) == 'unknown' else '', flush=True)
    if r == sat: print(fp.get_answer())
    if r == unsat: print(fp.get_answer())
