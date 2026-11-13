"""Collision table of a machine of the family by direct simulation (c/trans.c): for t = 2s + tp gaps of 2 after a
one-unit low part, a misaligned gap g, U gaps of 2 and a next gap h (or blank tape, h = None), print the blocks
appended to the word after phi twice, +2 on the last block and 3s ones, the new low part and the new gaps
(`h-5` = the next gap shortened by 5), for the values of h on which the outcome is uniform (at least 5 values of h
in 0..12, or blank tape).  `nonpref` = the word is rewritten further left; `X` = halt or step limit.
This is how the rows of TABLES in gen_collide.py were found; it proves nothing by itself.

usage: python3 collision_table.py MACHINE [UMAX]
"""
import subprocess
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hyb import binary


def tape(W, a, G):
    s = '0'.join('1' * b for b in W) + '0' + '1' * (3 * a)
    h = len(s)
    s += '0'
    for g in G:
        s += '0' * g + '1'
    return s, h


def go(W, a, G, maxs=10**7):
    s, h = tape(W, a, G)
    out = subprocess.run([binary('trans')], input=f"{M} {maxs} {h} B {s}", capture_output=True, text=True).stdout
    L = [l for l in out.strip().split('\n') if not l.startswith('F ')]
    if not L[0].startswith('Q'):
        return L[0], None, None
    _, dn, fc, m = L[0].split()
    return int(dn), [int(x) for x in L[1].split()[1:]], (int(m) // 3, [int(x) for x in L[2].split()[1:]])


def phi(W):
    W=list(W); b=W.pop(); W[-1]+=2; W+= [1]*((b-1)//2); return W
M = sys.argv[1]
UM=int(sys.argv[2]) if len(sys.argv)>2 else 7
pre=[2,1,1,1,1,3,1,1,1]
sufs=[[1,1],[3,1],[1,3],[5,3],[3,7]]
def one(tp,g,U,h,s,suf):
    W=pre+suf; t=2*s+tp
    G=[2]*t+[g]+[2]*U+([h,8,14] if h is not None else [])
    dn,W2,c=go(W,1,G)
    if W2 is None: return ('X',str(dn)[:6])
    P=phi(phi(W)); P[-1]+=2
    if W2[:len(P)+3*s]!=P+[1]*(3*s): return ('nonpref',tuple(W2[len(W)-2:]))
    C=tuple(W2[len(P)+3*s:]); Gp=c[1]
    if h is None: return (C,c[0],tuple(Gp))
    if Gp[-2:]!=[8,14]: return (C,c[0],'tailbad',tuple(Gp))
    Gp=Gp[:-2]
    return (C,c[0],tuple(Gp[:-1])+(('h%+d'%(Gp[-1]-h)),) if Gp else ())
for tp in [0,1]:
  for g in [0,1]:
    for U in range(UM):
      row={}
      for h in [None]+list(range(0,13)):
        res=set(one(tp,g,U,h,s,suf) for s in range(3) for suf in sufs)
        row.setdefault(str(sorted(res,key=str)),[]).append(h)
      print('tp',tp,'g',g,'U',U)
      for k,v in row.items():
        if len(v)>=5 or v[0] is None: print("     h=",v[0],v[1] if len(v)>1 else "",k[:110])
