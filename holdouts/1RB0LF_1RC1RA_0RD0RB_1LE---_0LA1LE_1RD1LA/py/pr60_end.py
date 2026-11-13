import os; exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'pr60_prefix.py')).read().split("# 1. prefix")[0])
ah=1083197534374707740536733690
assert ah+6==28*2**85
b=56*2**85-3*85-31
s=(22,b); k=0
while True:
    t=aStep(*s)
    if t is None: break
    s=t;k+=1
print("their map from (22, 56*2^85-286): halts after",k,"steps at",s==(ah,ah+3))
n=(1,8,b);k=0
while True:
    t=F(n)
    if t is None: break
    n=t;k+=1
print("our F from p 8 (56*2^85-286): halts after",k,"nodes at p",n[1],n[2], n[1]==(ah-6)//2*2+6 or n[1]==(ah-6)//2)
P=2**63; b312=234881023*P+9223338835920932358
print("gap from last cut to that b:", b-b312)
