import sys
from symjump import P, Dep, round_events, jump
from fractions import Fraction as Fr
def show(marks):
    out=[]
    for t,p in marks:
        a=p.a; b=p.b
        if a==0: out.append(f"{t}{b}")
        else: out.append(f"{t}[{a}m{'+' if b>=0 else ''}{b}]")
    return " ".join(out)
v=int(sys.argv[1]); R=int(sys.argv[2]) if len(sys.argv)>2 else 99
w0=P(2**(v+1),2); w=w0; marks=[["G",P(0,1)],["M",w0-2]]
for r in range(1,R+1):
    try: w,marks=round_events(w,marks)
    except Dep as e: print("round",r,"depends on m:",e); break
    print(r, show(marks[1:]))
    if len(marks)==2 and marks[1][0]=="M" and marks[1][1]==w-2: break
