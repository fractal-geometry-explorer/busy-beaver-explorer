"""Symbolic one-record runs for 1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_0RE---.
A macro config is a list [n0, s1, n1, ..., sk, nk] with n = int or Lin, s in 'S','0','1'; tape = blank? n0 ... nk 1 E> blank.
The left end is either blank ('edge') or a context L (prefix unknown)."""
import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../../tools/py'))
from bbtools import symtm
from bbtools.symtm import Lin, Rep, Ctx, Blank, Config, parse_lin
from bbtools.machine import Machine, STATES
M='1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_0RE---'
m=Machine.parse(M)
E=STATES.index('E')
SEP={'S':[0,1,1,0,0],'0':[0],'1':[1]}
def lin(x): return x if isinstance(x,Lin) else Lin(x)
def to_tokens(c, edge):
    toks=[Blank()] if edge else [Ctx('L')]
    for i,t in enumerate(c):
        if i%2==0:
            n=lin(t)
            if n.is_const():
                toks+= [1,0]*n.k
            else: toks.append(Rep((1,0),n))
        else: toks+=SEP[t]
    toks.append(1)
    return toks
def norm(left):
    """left tokens -> list of atoms: ints and ('R',Lin) for (10)^n"""
    out=[]
    for t in left:
        if isinstance(t,(Ctx,Blank)): out.append(t); continue
        if isinstance(t,int): out.append(t); continue
        w,n=t.word,t.n
        if n.is_const():
            out+= list(w)*n.k; continue
        if w==(1,0): out.append(('R',n))
        elif w==(0,1): out+= [0,('R',n-1),1]
        elif w==(1,):
            raise ValueError('rep of 1')
        else: raise ValueError('word %s'%(w,))
    # merge literal 1 0 pairs into adjacent R
    changed=True
    while changed:
        changed=False
        for i in range(len(out)):
            if isinstance(out[i],tuple):
                if i>=2 and out[i-2]==1 and out[i-1]==0:
                    out[i-2:i+1]=[('R',out[i][1]+1)]; changed=True; break
                if i+2<len(out) and out[i+1]==1 and out[i+2]==0:
                    out[i:i+3]=[('R',out[i][1]+1)]; changed=True; break
                if i+1<len(out) and isinstance(out[i+1],tuple):
                    out[i:i+2]=[('R',out[i][1]+out[i+1][1])]; changed=True; break
    return out
def parse_blocks(atoms):
    """atoms (after the left ctx) -> macro list, or None if it does not parse"""
    c=[]; cur=Lin(0); i=0
    while i<len(atoms):
        a=atoms[i]
        if isinstance(a,tuple): cur=cur+a[1]; i+=1; continue
        if atoms[i:i+5]==[0,1,1,0,0]: c+=[cur,'S']; cur=Lin(0); i+=5; continue
        if atoms[i:i+2]==[1,0]: cur=cur+1; i+=2; continue
        c+=[cur,str(a)]; cur=Lin(0); i+=1
    c.append(cur)
    return c
def record(c, edge=False, maxmoves=200000):
    """run from the E-record of macro config c to the next one; returns (new config, steps) ; raises symtm exceptions"""
    toks=to_tokens(c,edge)
    cfg=Config(toks,E,[Blank()])
    first=[True]
    def stop(k):
        if first[0]: first[0]=False; return False
        return k.state==E and k.right==[Blank()] and k.left and k.left[-1]==1
    symtm.run(m,cfg,stop,max_moves=maxmoves,rotate=True)
    left=cfg.left[:-1]
    atoms=norm(left)
    lead=atoms[0]; atoms=atoms[1:]
    if isinstance(lead,Blank):
        # strip leading zeros (blank)
        while atoms and atoms[0]==0: atoms=atoms[1:]
    return parse_blocks(atoms), cfg.steps
def show(c):
    return ' '.join(str(t) for t in c)
if __name__=='__main__':
    y,w,z=Lin('y')+10,Lin('w')+10,Lin('z')+10
    x=Lin('x')+10
    for c in [[x,'0',y,'S',w,'S',z],[x,'1',y,'S',w,'S',z],[x,'0',y],[x,'1',y],[x,'0',y,'S',z]]:
        r,s=record(c); print(show(c),' -> ',show(r),'  steps',s)
