"""Run 1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA from a built tape: the head in state E on the blank left of
`1 a^x0 s1 a^x1 ...`, given as e.g. "5 S 100 D 210" (numbers are block lengths, S = 110, D = 110110).  Prints the
result (halt or rounds), the steps, and the tape at the next left-end visits.

usage: python3 try.py "1 S 100 D 210" "5 D 100" "3 S 40"
"""
import sys; import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from genacc import *
M='1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA'
names={'0111':'b','011':'c','01':'a'}
def show(tok): return ' '.join((names.get(w,w) if n==1 else f'{names.get(w,w)}^{n}') for w,n in tok)
def build(spec):
    tok=[['1',1]]
    for t in spec.split():
        if t=='S': tok+=[[c,1] for c in '110']
        elif t=='D': tok+=[[c,1] for c in '110110']
        else:
            n=int(t)
            if n>=2: tok.append(['01',n])
            elif n==1: tok+=[['0',1],['1',1]]
    return tok
def trial(spec, maxsteps=10**12, rounds=3):
    A=Acc(M,['0111','011','01'])
    A.s=Sim(M,build(spec),4,-1); A.s.dir=-1  # E at left blank
    out=[]
    def on(a,key,j):
        if key[1]=='L': out.append(show(a.s.tok))
        if len(out)>=rounds: raise StopIteration
    try: r=A.run(maxsteps,on)
    except StopIteration: r='rounds'
    return r,A.s.steps,out
if __name__=='__main__':
    for spec in sys.argv[1:]:
        r,st,out=trial(spec)
        print(spec,'=>',r,st); [print('   ',o[:150]) for o in out]
