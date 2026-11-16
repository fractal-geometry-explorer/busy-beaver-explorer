"""Affine forms c + sum a_i*y_i over variables y_i >= 0 (integers), with decidable comparisons only."""
from math import gcd
class Undecided(Exception):
    def __init__(s, vars): s.vars=set(vars)
class NeedMod(Exception):
    def __init__(s, var, m): s.var=var; s.m=m
class NonLinear(Exception): pass
def mk(c, co):
    co={v:a for v,a in co.items() if a}
    return Lin(c,co) if co else c
class Lin:
    __slots__=('c','co')
    def __init__(s,c,co): s.c=c; s.co=co
    def __add__(s,o):
        if isinstance(o,Lin):
            co=dict(s.co)
            for v,a in o.co.items(): co[v]=co.get(v,0)+a
            return mk(s.c+o.c,co)
        return Lin(s.c+o,s.co)
    __radd__=__add__
    def __neg__(s): return Lin(-s.c,{v:-a for v,a in s.co.items()})
    def __sub__(s,o): return s+(-o)
    def __rsub__(s,o): return (-s)+o
    def __mul__(s,o):
        if isinstance(o,Lin): raise NonLinear()
        return mk(s.c*o,{v:a*o for v,a in s.co.items()})
    __rmul__=__mul__
    def _divcheck(s,m):
        for v,a in s.co.items():
            if a%m: raise NeedMod(v, m//gcd(a,m))
    def __floordiv__(s,m):
        if isinstance(m,Lin): raise NonLinear()
        s._divcheck(m); return mk(s.c//m,{v:a//m for v,a in s.co.items()})
    def __mod__(s,m):
        if isinstance(m,Lin): raise NonLinear()
        s._divcheck(m); return s.c%m
    def _sign(s):  # returns ('+',strict) etc.
        pos=all(a>0 for a in s.co.values()); neg=all(a<0 for a in s.co.values())
        if pos: return 1 if s.c>0 else (2 if s.c==0 else None)   # 1: >0 ; 2: >=0
        if neg: return -1 if s.c<0 else (-2 if s.c==0 else None)
        return None
    def _cmp(s,o):
        d=s-o
        if not isinstance(d,Lin): return (d>0)-(d<0), True
        r=d._sign()
        if r is None: raise Undecided(d.co)
        return r, d
    def __eq__(s,o):
        d=s-o
        if not isinstance(d,Lin): return d==0
        r=d._sign()
        if r in (1,-1): return False
        raise Undecided(d.co)
    def __ne__(s,o): return not s.__eq__(o)
    def __gt__(s,o):
        d=s-o
        if not isinstance(d,Lin): return d>0
        r=d._sign()
        if r==1: return True
        if r in (-1,-2): return False
        raise Undecided(d.co)
    def __ge__(s,o):
        d=s-o
        if not isinstance(d,Lin): return d>=0
        r=d._sign()
        if r in (1,2): return True
        if r==-1: return False
        raise Undecided(d.co)
    def __lt__(s,o): return not s.__ge__(o)
    def __le__(s,o): return not s.__gt__(o)
    __hash__=None
    def __repr__(s): return f"({s.c}"+''.join(f"+{a}*y{v}" for v,a in sorted(s.co.items()))+")"
def same(a,b):
    """identical as forms (used for representation choices only)"""
    d=a-b
    return (not isinstance(d,Lin)) and d==0
def is_sym(x): return isinstance(x,Lin)
def ev(x, vals):
    if isinstance(x,Lin): return x.c+sum(a*vals[v] for v,a in x.co.items())
    return x
