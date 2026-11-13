"""Plain simulator for one round of 1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA: from the left-end tape with blocks
`bl` (E> 0 1 a^x0 110 a^x1 ... 110 a^xk, a = 01) to the next visit of the left end in state E.

rnd(bl) = (next list of blocks, steps), ('halt', steps), or (('junk', cells), steps) when the next left-end tape is
not of that form.     usage: python3 direct.py 9 7 5
"""
M='1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA'
T=[]
for i,g in enumerate(M.split('_')):
    for b in (0,1):
        s=g[3*b:3*b+3]
        T.append(None if s[0]=='-' else (int(s[0]),1 if s[1]=='R' else -1,ord(s[2])-65))
def build(bl):
    t='1'
    for i,n in enumerate(bl):
        if i: t+='110'
        t+='01'*n
    return t
def parse(cells):
    s=''.join(map(str,cells)).strip('0')
    if not s.startswith('1'): return None
    s=s[1:]; blocks=[0]; j=0
    while j<len(s):
        if s.startswith('01',j): blocks[-1]+=1; j+=2
        elif s.startswith('110',j): blocks.append(0); j+=3
        else: return ('junk',s)
    return blocks
def rnd(bl, maxst=10**8):
    t=build(bl); OFF=maxst//1000+len(t)+100
    N=2*OFF+len(t)+10
    tape=bytearray(N)
    for i,c in enumerate(t): tape[OFF+i]=int(c)
    pos=OFF-1; q=4; st=0; minone=OFF
    while st<maxst:
        b=tape[pos]; tr=T[2*q+b]
        if tr is None: return 'halt',st
        w,d,q=tr
        tape[pos]=w
        if w==1 and pos<minone: minone=pos
        pos+=d; st+=1
        if q==4 and pos<minone and st>1:
            if tape[pos]==0:
                return parse(tape[pos:]), st
        if pos<=0 or pos>=N-1: return 'overflow',st
    return 'max',st
if __name__=='__main__':
    import sys
    print(rnd([int(x) for x in sys.argv[1:]]))
