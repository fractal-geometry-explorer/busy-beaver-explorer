"""Shape-level (counts symbolic) exploration of the odometer rounds of the 1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA?RF_F--- family.

usage: python3 shapes.py MACHINE DEPTH [EXTRA_ATOMS]
   e.g. python3 shapes.py 1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1RC--- 3 1,10,100,1001101,10011010,10011011,100110110,1001101100

A macro configuration is the head in D on the first cell of `b^(k+1) G1 b^n1 G2 ...` (b = 1000), the gadgets Gi taken
from an alphabet of atoms (g0..g4, s and EXTRA_ATOMS) and every block either empty or symbolic (n+1).  For every
prefix of up to DEPTH gadgets this runs the real machine symbolically (bbtools.symtm, shift rules on) until the head is
back in D at the left end, splitting a count into 0 / >=1 whenever the run needs it, and extending the prefix when the
run touches the unknown rest of the tape.  It reports the atoms the results need that are not in the alphabet, the
prefixes that halt (F reading 1), and the prefixes still unresolved at DEPTH (carry chains through g3 and runs of
empty blocks).  With the atoms above the alphabet is closed (no new atoms at depths 2 and 3), but every machine has
halting prefixes: all of them contain the stretch `101` (the atom `10` meeting a gadget across an empty block), or
for 1RD/0RC/1RE also `10 b^1 ...`; see lean/Escape.lean for the kernel-checked trap and a halting witness.
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'tools', 'py'))
from bbtools.symtm import Config, run, Machine, Rep, Blank, Ctx, canon, Lin, TouchContext, NeedSplit, Halted, STATES
def at_left_D(c):
    if c.steps.is_zero() or STATES[c.state]!='D': return False
    L=canon(c.left)
    if not (L==[Blank()] or L==[]): return False
    cells=[]
    for t in c.right:
        if isinstance(t,int): cells.append(t)
        elif isinstance(t,Rep):
            if not t.n.surely_ge(1): return False
            cells+=list(t.word)
        else: break
        if len(cells)>=4: break
    return cells[:4]==[1,0,0,0]

import itertools
from bbtools.symtm import Config, run, Machine, Rep, Blank, Ctx, canon, Lin, TouchContext, NeedSplit, Halted, STATES, tokens
B=(1,0,0,0)
def cfg_of(prefix, tail):
    """prefix: list alternating Lin/int blocks and stretch strings, starting with a block; tail 'R' or 'END'"""
    toks=[Blank()]
    for x in prefix:
        if isinstance(x,str): toks+= [int(c) for c in x]
        else: toks.append(Rep(B, x if isinstance(x,Lin) else Lin(x)))
    toks.append(Ctx('R') if tail=='R' else Blank())
    return toks
def subs_toks(toks, v, e):
    out=[]
    for t in toks:
        if isinstance(t,Rep) and v in t.n.vars():
            out.append(Rep(t.word, t.n.subs({v:e}) if hasattr(t.n,'subs') else t.n))
        else: out.append(t)
    return out
def lsub(L, v, e):
    env={x:(e if x==v else Lin(x)) for x in L.vars()}
    r=Lin(L.k)
    for x,a in L.c.items(): r=r+a*env[x]
    return r
def norm_b(right):
    """rebracket rotations of 1000 to (1000)^n; returns list of ints and Rep(B,..), plus tail"""
    R=list(right)
    tail=None
    if R and isinstance(R[-1],Ctx): tail='R'; R=R[:-1]
    elif R and isinstance(R[-1],Blank): tail='END'; R=R[:-1]
    else: raise ValueError('bad tail %r'%(R[-1:],))
    out=[]
    i=0
    # expand constant reps
    E=[]
    for t in R:
        if isinstance(t,Rep):
            if t.n.is_const(): E+=list(t.word)*t.n.k
            else:
                if t.n.k: E.append(Rep(t.word,Lin(0,t.n.c))); E+=list(t.word)*t.n.k
                else: E.append(t)
        else: E.append(t)
    changed=True
    while changed:
        changed=False
        for j,t in enumerate(E):
            if isinstance(t,Rep) and t.word!=B:
                w=t.word
                r=next((r for r in range(1,4) if B[r:]+B[:r]==w),None)
                if r is None: raise ValueError('non-b rep %r'%(t,))
                pre=tuple(B[:r]); post=tuple(B[r:])
                if j>=r and all(isinstance(x,int) for x in E[j-r:j]) and tuple(E[j-r:j])==pre:
                    E[j-r:j+1]=[Rep(B,t.n)]+list(pre); changed=True; break
                if all(isinstance(x,int) for x in E[j+1:j+1+len(post)]) and tuple(E[j+1:j+1+len(post)])==post:
                    E[j:j+1+len(post)]=list(post)+[Rep(B,t.n)]; changed=True; break
                raise ValueError('cannot rebracket %r'%(E,))
    return E, tail
def parse_right(right):
    E,tail=norm_b(right)
    # string with placeholders
    out=[]; cur=''
    for t in E:
        if isinstance(t,int): cur+=str(t)
        else: out.append(cur); out.append(t.n); cur=''
    out.append(cur)
    def split_bits(s):
        parts=[]; i=0; cur=''
        while i<len(s):
            if s.startswith('1000',i):
                n=0
                while s.startswith('1000',i): n+=1; i+=4
                parts.append(cur); parts.append(Lin(n)); cur=''
            else: cur+=s[i]; i+=1
        parts.append(cur); return parts
    flat=[]
    for x in out:
        if isinstance(x,str): flat+=split_bits(x)
        else: flat.append(x)
    merged=[]
    for x in flat:
        if isinstance(x,str):
            if merged and isinstance(merged[-1],str): merged[-1]+=x
            else: merged.append(x)
        else:
            if len(merged)>=2 and merged[-1]=='' and not isinstance(merged[-2],str):
                merged.pop(); merged[-1]=merged[-1]+x
            else: merged.append(x)
    return merged, tail
def round_(M, prefix, tail, maxm=200000):
    m=Machine.parse(M)
    c=Config([], 3, cfg_of(prefix,tail))
    c.left=[Blank()]; c.right=c.right[1:]
    try:
        f=run(m,c,at_left_D,max_moves=maxm)
    except TouchContext as e: return ('touch',None)
    except NeedSplit as e: return ('split',e.args[0])
    except Halted as e: return ('halt',str(e))
    except RuntimeError as e: return ('loop',str(e)[:200])
    return ('ok',f)

import functools
M=sys.argv[1]; MAXD=int(sys.argv[2]) if len(sys.argv)>2 else 4
GAM={"g0":"1001","g1":"1001100","g2":"100110","g3":"10011","g4":"10010","s":"0"}
extra=sys.argv[3].split(',') if len(sys.argv)>3 and sys.argv[3] else []
for i,x in enumerate(extra): GAM['x'+x]=x
LAST=set(['g0'])
cnt=itertools.count()
def nv(): return Lin('v%d'%next(cnt))
def split(s):
    @functools.lru_cache(None)
    def sp(s):
        if s=="": return ()
        best=None
        for n,w in sorted(GAM.items(),key=lambda x:-len(x[1])):
            if s.startswith(w):
                r=sp(s[len(w):])
                if r is not None: return (n,)+r
        return None
    return sp(s)
stats=dict(deep=[],halts=[],newatoms=set(),newlast=set(),other=[],loops=[],chains=0,rounds=0)
def mk(units, tail):
    """units: list of (gadget, block) ; block Lin or 0 ; returns prefix list for eng"""
    pre=['', nv()+1]
    for g,b in units:
        w=GAM[g]
        if isinstance(pre[-1],str): pre[-1]+=w
        else: pre.append(w)
        if b is not None:
            if isinstance(b,int) and b==0: pass
            else: pre.append(b)
    return pre
def exts(units):
    for g in GAM:
        yield units+[(g,nv()+1)],'R'
        yield units+[(g,0)],'R'
    for g in LAST:
        yield units+[(g,None)],'END'
def check_result(res,rt):
    strs=[x for x in res if isinstance(x,str)]
    if strs[0]!='': stats['other'].append(('lead',res)); return
    for i,S in enumerate(strs[1:]):
        if i==len(strs)-2:
            if rt=='R':
                if S!='': return 'extend'
                continue
            sp=split(S)
            if sp is None: stats['newlast'].add(S)
            else:
                if sp[-1] not in LAST: stats['newlast'].add(GAM[sp[-1]])
            continue
        if split(S) is None: stats['newatoms'].add(S)
def explore(units, tail, pre=None):
    if pre is None: pre=mk(units,tail)
    r,info=round_(M,pre,tail)
    if r=='touch':
        if tail!='R': stats['other'].append(('touch-end',pre)); return
        if len(units)>=MAXD: stats['deep'].append(pre); return
        for u,t in exts(units): explore(u,t)
        return
    if r=='split':
        v=list(info.n.vars())[0]
        explore(units,tail,[x if isinstance(x,str) else lsub(x,v,Lin(0)) for x in pre] and fixz([x if isinstance(x,str) else lsub(x,v,Lin(0)) for x in pre]))
        explore(units,tail,[x if isinstance(x,str) else lsub(x,v,Lin(v)+1) for x in pre])
        return
    if r=='halt': stats['halts'].append((pre,tail,info)); return
    if r=='loop': stats['loops'].append((pre,tail)); return
    stats['rounds']+=1
    try: res,rt=parse_right(info.right)
    except Exception as e: stats['other'].append(('parse',pre,str(e)[:200])); return
    for x in res:
        if not isinstance(x,str) and not x.surely_ge(1):
            if not x.vars(): break
            v=list(x.vars())[0]
            explore(units,tail,fixz([y if isinstance(y,str) else lsub(y,v,Lin(0)) for y in pre]))
            explore(units,tail,[y if isinstance(y,str) else lsub(y,v,Lin(v)+1) for y in pre])
            return
    if check_result(res,rt)=='extend':
        if len(units)>=MAXD: stats['deep'].append(pre); return
        # the prefix ended with a block that became empty: extend with the next unit
        for u,t in exts(units): explore(u,t)
def fixz(prefix):
    out=[]
    for x in prefix:
        if not isinstance(x,str) and x.is_zero(): continue
        if isinstance(x,str) and out and isinstance(out[-1],str): out[-1]+=x
        else: out.append(x)
    return out
for g in GAM:
    explore([(g,nv()+1)],'R'); explore([(g,0)],'R')
for g in LAST: explore([(g,None)],'END')
print('rounds',stats['rounds'],'deep',len(stats['deep']),'halts',len(stats['halts']),'other',len(stats['other']),'loops',len(stats['loops']))
print('newatoms',sorted(stats['newatoms'],key=len)[:40])
print('newlast',sorted(stats['newlast'],key=len)[:40])
from collections import Counter
def shape(p): return ' '.join(x if isinstance(x,str) else 'n' for x in p)
print('deep shapes:'); 
for s,c in Counter(shape(p) for p in stats['deep']).most_common(30): print(' ',c,s)
for h in stats["halts"]: print('HALT',h)
for o in stats['other'][:5]: print('OTHER',o)
