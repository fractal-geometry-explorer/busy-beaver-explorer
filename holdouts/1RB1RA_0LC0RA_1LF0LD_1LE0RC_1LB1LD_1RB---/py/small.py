import sys, itertools
M="1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---"
T={}
for s,part in enumerate(M.split('_')):
    for r in range(2):
        t=part[3*r:3*r+3]
        T[(s,r)]=None if t[2]=='-' else (int(t[0]),1 if t[1]=='R' else -1,ord(t[2])-65)
def run(cells,pos,st,maxs=200000):
    tape=dict(enumerate(cells));p=pos
    for k in range(maxs):
        tr=T[(st,tape.get(p,0))]
        if tr is None: return k
        tape[p]=tr[0];p+=tr[1];st=tr[2]
    return None
# the concrete config from the abstract path: left 1 0 1 0 1, B on blank
print('10101[B]:', run([1,0,1,0,1],5,1))
# all tapes with single zeros between blocks (blocks 1..4), up to 4 blocks, every head position (incl. one beyond each end) and state
res={}
for nb in range(1,5):
    for bl in itertools.product(range(1,5),repeat=nb):
        cells=[]
        for b in bl: cells+=[1]*b+[0]
        cells=cells[:-1]
        for st in range(6):
            for pos in range(-1,len(cells)+1):
                h=run(cells,pos,st,20000)
                if h is not None: res.setdefault('ABCDEF'[st],[]).append((bl,pos,h))
for st in res: print(st,len(res[st]),res[st][:6])
# smallest example found: blocks 3, 2 (cells 111011), A on the first cell: halts (F reads 1) after 655 steps
print('111011, A at the left end:', run([1,1,1,0,1,1],0,0))
