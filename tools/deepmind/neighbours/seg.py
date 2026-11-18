"""Run a machine from a configuration whose outer tape is symbolic (unreadable) or blank, and check that it reaches a
target configuration in >= 1 steps without reading the symbolic part.  Used to re-check DeepMind's step lemmas
(proved in Lean by `execute`/`decide` on symbolic tails) on a neighbouring table."""
# Symbolic-tail checker for DeepMind WordVKQ-style lemmas: run machine from a config with
# symbolic tails (unreadable) or blank tails, and check it reaches the target config (>=1 step).
import sys
def parse(m):
    T={}
    for q,row in enumerate(m.split('_')):
        for b in (0,1):
            t=row[3*b:3*b+3]
            T[(q,b)]=None if t[0]=='-' else (int(t[0]),1 if t[1]=='R' else -1,ord(t[2])-65)
    return T
# config: (state, left list nearest-first, head sym, right list nearest-first, ltail, rtail)
# tails: 'B' blank or a name string (symbolic)
def R(l,q,r,lt,rt):  # head reads r[0]  ( l {{q}}> r )
    return (q, list(l), r[0], list(r[1:]), lt, rt)
def L(l,q,r,lt,rt):  # head reads l[0]  ( l <{{q}} r )
    return (q, list(l[1:]), l[0], list(r), lt, rt)
def norm(c):
    q,l,h,r,lt,rt=c
    l=list(l); r=list(r)
    if lt=='B':
        while l and l[-1]==0: l.pop()
    if rt=='B':
        while r and r[-1]==0: r.pop()
    return (q,tuple(l),h,tuple(r),lt,rt)
def run(T,c,target,maxsteps=10**6):
    q,l,h,r,lt,rt=c; l=list(l); r=list(r); tgt=norm(target)
    for s in range(1,maxsteps+1):
        if h is None: return ('readsym',s)
        t=T[(q,h)]
        if t is None: return ('halt',s)
        w,d,q=t
        if d==1:
            l.insert(0,w)
            if r: h=r.pop(0)
            elif rt=='B': h=0
            else: h=None
        else:
            r.insert(0,w)
            if l: h=l.pop(0)
            elif lt=='B': h=0
            else: h=None
        if h is not None and norm((q,l,h,r,lt,rt))==tgt: return ('ok',s)
        if h is None and target[2] is None and norm((q,l,None,r,lt,rt))==tgt: return ('ok',s)
    return ('timeout',maxsteps)
