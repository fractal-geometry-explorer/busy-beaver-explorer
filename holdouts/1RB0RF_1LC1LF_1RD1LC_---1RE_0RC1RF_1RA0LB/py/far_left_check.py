"""The counter value at the first counter configuration after given steps (the far-left visits found with
tmrun ... at F L): python3 py/far_left_check.py 3682344 5522782 9203628 68017235 185638122 303258880 538500366
(about 4 minutes).  Output: request step, step of the configuration, n, n in binary."""
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from sim import TM
times=[int(x) for x in sys.argv[1:]]
t=TM('1RB0RF_1LC1LF_1RD1LC_---1RE_0RC1RF_1RA0LB',1<<16); tape=t.tape
c=len(tape)//2+77
for T in times:
    while t.k<T: t.step()
    # next counter config at c
    while True:
        st=t.st; t.step()
        if st==2 and t.st==3 and t.p==c and tape[t.p]==1 and bytes(tape[c:c+5])==b'\x01'*5:
            q=c+5;n=0;i=0
            while True:
                w=bytes(tape[q:q+4])
                if w==b'\x01\x00\x01\x01': n|=1<<i
                elif w!=b'\x01'*4: break
                q+=4;i+=1
            print(T,t.k,n,bin(n),flush=True); break
