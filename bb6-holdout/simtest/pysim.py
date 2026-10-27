"""Run the round function of one of the Python certificate checkers (../cert/check_*.py) on concrete round starts.

usage: python3 pysim.py CHECKER NR < starts > rounds      (same line formats as Oracle.lean)
CHECKER is a path to check_endgame.py, check_exit.py or check_tree.py; only the definitions before the checker's
main section are loaded.  A configuration the checker refuses (Uncovered, Undecided, or its early return at a close)
is reported as U, a packet reaching a block as H."""
import re, sys

def load(path):
    src = open(path).read().split('\n')
    cut = next(i for i, l in enumerate(src) if re.match(r'(leaves = |pat = re\.compile)', l))
    ns = {'__name__': 'checker'}
    exec(compile('\n'.join(src[:cut]), path, 'exec'), ns)
    return ns

class AnyOutcome(int):
    """a recorded meeting outcome that matches whatever the class decides (check_tree replays recorded outcomes)"""
    def __ne__(self, other): return False
    def __eq__(self, other): return True
    __hash__ = int.__hash__

def make_runner(ns, kind):
    form, isconst = ns['form'], ns['isconst']
    if kind == 'tree':
        SC = ns['SC']
        def mk(c): return form(0, 0, c)
        def val(p): assert isconst(p) and p[2] % SC == 0; return p[2] // SC
        cos = lambda: ns['Coset']([0, 0], [[0, 0], [0, 0]])
        outs = [AnyOutcome(0)] * 100000
        def rnd(marks, W): return ns['run_round'](marks, W, cos(), outs, [0], [])
    else:
        nvar = 3 if kind == 'endgame' else 4
        def mk(c): return form(c0=c)
        def val(p): assert isconst(p) and p[-1].denominator == 1; return int(p[-1])
        cos = lambda: ns['Coset']([0] * nvar, [[0] * nvar for _ in range(nvar)])
        def rnd(marks, W):
            marks, W, meets, closed = ns['run_round'](marks, W, cos(), 0, None)
            if closed: raise ns['Uncovered']('close (the checker stops the round there)')
            return marks, W
    return mk, val, rnd

def simulate(ns, kind, W0, ms, nr):
    mk, val, rnd = make_runner(ns, kind)
    marks = [['G', mk(1)]] + [[t, mk(p)] for t, p in ms]; W = mk(W0); out = []
    for _ in range(nr):
        try:
            marks, W = rnd(marks, W)
        except ns['Uncovered'] as e:
            return out + ['H' if 'halt' in str(e) else 'U']
        except ns['Undecided']:
            return out + ['U']
        vals = [(t, val(p)) for t, p in marks]
        if not vals or vals[0] != ('G', 1): return out + ['U']
        out.append(' '.join(['R', str(val(W))] + ['%s %d' % tp for tp in vals[1:]]))
    return out + ['E']

if __name__ == '__main__':
    path, nr = sys.argv[1], int(sys.argv[2])
    kind = 'tree' if 'tree' in path else 'exit' if 'exit' in path else 'endgame'
    ns = load(path)
    for line in sys.stdin:
        w = line.split(); W0 = int(w[0]); ms = [(w[i], int(w[i + 1])) for i in range(1, len(w), 2)]
        for s in simulate(ns, kind, W0, ms, nr): print(s)
        print('.', flush=True)
