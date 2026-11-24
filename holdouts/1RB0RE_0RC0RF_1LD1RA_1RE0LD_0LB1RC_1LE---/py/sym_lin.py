"""affine forms over nonnegative integer variables; decisions raise Need for case splits"""
class Lin:
    __slots__=("c","k")
    def __init__(s, k=0, c=None):
        s.k=k; s.c={v:x for v,x in (c or {}).items() if x}
    @staticmethod
    def var(v): return Lin(0,{v:1})
    def __add__(s,o):
        o=L(o); c=dict(s.c)
        for v,x in o.c.items(): c[v]=c.get(v,0)+x
        return Lin(s.k+o.k,c)
    __radd__=__add__
    def __neg__(s): return Lin(-s.k,{v:-x for v,x in s.c.items()})
    def __sub__(s,o): return s+(-L(o))
    def __rsub__(s,o): return L(o)-s
    def __mul__(s,n):
        assert isinstance(n,int); return Lin(s.k*n,{v:x*n for v,x in s.c.items()})
    __rmul__=__mul__
    def key(s): return (s.k,tuple(sorted(s.c.items())))
    def __eq__(s,o): return isinstance(o,(Lin,int)) and s.key()==L(o).key()
    def __hash__(s): return hash(s.key())
    def isconst(s): return not s.c
    def __repr__(s):
        t=[(f"{x}{v}" if x!=1 else v) for v,x in sorted(s.c.items())]
        if s.k or not t: t.append(str(s.k))
        return "+".join(t).replace("+-","-")
    def subst(s,v,e):
        if v not in s.c: return s
        x=s.c[v]; c=dict(s.c); del c[v]
        return Lin(s.k,c)+L(e)*x
    def ev(s,env): return s.k+sum(x*env[v] for v,x in s.c.items())
def L(x): return x if isinstance(x,Lin) else Lin(x)
class Need(Exception):
    """a case split: a list of substitutions (var, Lin) covering all values of var"""
    def __init__(s,cases): s.cases=cases
CTX=[]   # constraints (Lin >= 0) of the current path
_z3=None
def _sat(cons):
    """Fourier-Motzkin over the rationals: False only if the constraints (each Lin >= 0, all vars >= 0) have no
    rational solution, hence no integer one.  (Sound for deciding: a decision is only taken on False.)"""
    from fractions import Fraction
    rows=[]
    vs=set()
    for e in cons: vs|=set(e.c)
    for e in cons: rows.append(({v:Fraction(x) for v,x in e.c.items()},Fraction(e.k)))
    for v in vs: rows.append(({v:Fraction(1)},Fraction(0)))
    for v in sorted(vs):
        pos=[r for r in rows if r[0].get(v,0)>0]; neg=[r for r in rows if r[0].get(v,0)<0]
        rest=[r for r in rows if r[0].get(v,0)==0]
        for cp,kp in pos:
            for cn,kn in neg:
                a=cp[v]; b=-cn[v]
                c={}
                for w in set(cp)|set(cn):
                    if w==v: continue
                    x=cp.get(w,0)*b+cn.get(w,0)*a
                    if x: c[w]=x
                rest.append((c,kp*b+kn*a))
        rows=rest
        if len(rows)>4000: return True   # give up: claim satisfiable (no decision)
    return all(k>=0 for c,k in rows if not c)
def ge(e,c=0):
    e=L(e)-c
    if e.k>=0 and all(x>=0 for x in e.c.values()): return True
    if e.k<0 and all(x<=0 for x in e.c.values()): return False
    if CTX:
        if not _sat(CTX+[-e-1]): return True
        if not _sat(CTX+[e]): return False
    if len(e.c)>1:
        raise Need([("C",e),("C",-e-1)])
    # split the variable that can settle it: v = 0 | v >= 1
    v=min(e.c, key=lambda v:(e.c[v]>0) == (e.k<0))  # a var whose sign opposes the constant
    v=sorted(e.c)[0] if v is None else v
    raise Need([(v,Lin(0)),(v,Lin.var(v)+1)])
def eq(e,c): return ge(e,c) and not ge(e,c+1)
def lt(e,c): return not ge(e,c)
_fresh=[0]
def fresh(p="x"):
    _fresh[0]+=1; return f"{p}{_fresh[0]}"
def divmod_(e,q):
    """(e // q, e % q) when decided; split on residues otherwise"""
    e=L(e)
    for v,x in sorted(e.c.items()):
        if x%q:
            raise Need([(v,Lin.var(v)*q+r) for r in range(q)])
    return Lin(e.k//q,{v:x//q for v,x in e.c.items()}), e.k%q
def mod(e,q): return divmod_(e,q)[1]
def subst_obj(o,v,e):
    if isinstance(o,Lin): return o.subst(v,e)
    if isinstance(o,tuple): return tuple(subst_obj(x,v,e) for x in o)
    if isinstance(o,list): return [subst_obj(x,v,e) for x in o]
    if isinstance(o,dict): return {k:subst_obj(x,v,e) for k,x in o.items()}
    return o
def ev_obj(o,env):
    if isinstance(o,Lin): return o.ev(env)
    if isinstance(o,tuple): return tuple(ev_obj(x,env) for x in o)
    if isinstance(o,list): return [ev_obj(x,env) for x in o]
    return o
