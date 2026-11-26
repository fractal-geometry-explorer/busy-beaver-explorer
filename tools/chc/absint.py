"""Predicate-abstraction search for an inductive invariant of a counter program (maps.py).
Abstract value of a term t: exact if -T <= t < T, else (sign, t mod M).  Abstract state: tuple over the variables and
optional extra linear terms.  Reachable abstract states are enumerated with Z3 (sound for the domain); if no reachable
abstract state meets a bad guard, the disjunction of the states is an inductive invariant (re-checked independently)."""
import sys, time, itertools
from z3 import *
from maps import M, EXTRA  # noqa

def absval(t, T, Mo):
    if -T <= t < T: return ('e', t)
    return ('b' if t >= T else 'n', t % Mo)
def gamma(term, a, T, Mo):
    if a[0] == 'e': return term == a[1]
    return And(term >= T, term % Mo == a[1]) if a[0] == 'b' else And(term < -T, term % Mo == a[1])

def search(name, T, Mo, limit=20000, verbose=False):
    n, start, rules = M[name]
    v = [Int('x%d' % i) for i in range(n)]; w = [Int('y%d' % i) for i in range(n)]
    ex = EXTRA.get(name, lambda v: [])
    tv = v + ex(v); tw = w + ex(w)
    R = rules(v)
    def al(vals): 
        s = Solver(); s.add([x == c for x, c in zip(v, vals)]); assert s.check() == sat; m = s.model()
        return tuple(absval(m.eval(t, model_completion=True).as_long(), T, Mo) for t in tv)
    a0 = al(start); seen = {a0}; todo = [a0]
    while todo:
        a = todo.pop()
        ga = And([gamma(t, x, T, Mo) for t, x in zip(tv, a)])
        for g, tgt in R:
            s = Solver(); s.add(ga, g)
            if tgt == 'halt':
                if s.check() == sat:
                    if verbose: print('  bad at', a, s.model())
                    return None, len(seen)
                continue
            s.add([y == e for y, e in zip(w, tgt)])
            while s.check() == sat:
                m = s.model()
                b = tuple(absval(m.eval(t, model_completion=True).as_long(), T, Mo) for t in tw)
                if b not in seen:
                    seen.add(b); todo.append(b)
                    if len(seen) > limit: return None, len(seen)
                s.add(Not(And([gamma(t, x, T, Mo) for t, x in zip(tw, b)])))
    return seen, len(seen)

if __name__ == '__main__':
    names = [sys.argv[1]] if sys.argv[1] != 'all' else list(M)
    for name in names:
        ok = False; t0 = time.time()
        for Mo in [1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 27, 36]:
            for T in [4, 8, 16, 32]:
                if time.time() - t0 > int(sys.argv[2]): break
                inv, cnt = search(name, T, Mo, limit=3000)
                if inv:
                    print(name, 'INVARIANT', 'T', T, 'M', Mo, 'states', cnt, flush=True); ok = True
                    for a in sorted(inv, key=str): print('   ', a)
                    break
            if ok: break
        if not ok: print(name, 'no invariant in this domain', '%.0fs' % (time.time() - t0), flush=True)
