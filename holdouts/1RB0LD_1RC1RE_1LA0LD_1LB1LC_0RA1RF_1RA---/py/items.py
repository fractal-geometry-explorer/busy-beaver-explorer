"""Item-level model of 1RB0LD_1RC1RE_1LA0LD_1LB1LC_0RA1RF_1RA--- (see ../README.md), and its checks.

At a sweep start the head is in state D on the leftmost cell (a 0) and the tape to its right is
    0 (10)^n0 s0 (10)^n1 s1 ... (10)^nk sk          s0 = 0, sk = 1,
the item list [(n0, s0), ..., (nk, sk)].  `model` does one sweep (the parity-signal rule and the four special
sweeps), `model_steps` its exact step count; `cell_sweep` runs one sweep cell by cell.

usage: python3 py/items.py check      the model against cell-level sweeps (random item lists) and against a direct
                                      run from blank tape (every sweep start of the first 3,000,000 steps)
"""
import sys, time
M='1RB0LD_1RC1RE_1LA0LD_1LB1LC_0RA1RF_1RA---'
TAB={}
for i,g in enumerate(M.split('_')):
    for s in (0,1):
        t=g[3*s:3*s+3]
        TAB[(i,s)]=None if t[0]=='-' else (int(t[0]),1 if t[1]=='R' else -1,ord(t[2])-65)
def model(it):
    """returns (new items, kind) or None when the sweep is not modelled; kind: ('reg', d), ('reset', i),
    ('merge', i), ('xend', i), ('yend', i)"""
    sig = 0 if it[0][0]%2==0 else 1   # 0 = X (act), 1 = Y (pass)
    i=1
    ch={}
    L=len(it)
    def get(j): return ch.get(j, it[j])
    while i<L:
        n,s=get(i)
        if s=='E': return None
        if sig==0:
            if n>=1: ch[i]=(n-1,s); kind=('reg',i); break
            if s==0:
                if not ch and i+1<L and all(it[j][1]==0 for j in range(i)) and i>=1:
                    new=[(2,0)]+[(it[j][0],1) for j in range(i-1)]+[(it[i-1][0]+1,1)]+list(it[i+1:])
                    k=i
                    if new[k][1]==1 and k+1<len(new) and new[k+1]==(0,0) and k+2<len(new):
                        new[k:k+3]=[(new[k][0]+1+new[k+2][0],new[k+2][1])]
                    return new, ('reset',i)
                return None
            # X at (0,1)
            p,ps=get(i-1)
            if ps!=0 or i<2: return None
            new=[get(j) for j in range(L)]
            if i==L-1:
                if p<1: return None
                new[i-1:]=[(p-1,1)]
                new[0]=(it[0][0]+3,0)
                return new, ('xend',i)
            m,ms=get(i+1)
            new[i-1:i+2]=[(p+m,ms)]
            new[0]=(it[0][0]+3,0)
            return new, ('merge',i)
        if s==0:
            sig = 0 if n%2==0 else 1
        else:
            if i==L-1:
                if ch or not all(it[j][1]==0 for j in range(i)): return None
                new=[(2,0)]+[(it[j][0],1) for j in range(i)]
                new += [(n+2,1)] if n%2==1 else [(n+1,1),(1,1)]
                return new, ('yend',i)
            if n%2==1: ch[i]=(n,0)
            else:
                if it[i+1][0]<1 or it[i+1][1]=='E': return None
                ch[i]=(n+1,0); ch[i+1]=(it[i+1][0]-1,it[i+1][1])
            sig=0
        i+=1
    else:
        return None
    new=list(it)
    for j,v in ch.items(): new[j]=v
    new[0]=(it[0][0]+3,0)
    return new, kind
def model_steps(it, kind):
    """steps of a modelled sweep (fitted, checked against cell_sweep)"""
    k, d = kind
    if k == 'reset':
        return reset_steps(it, d)
    if k == 'yend':
        return 3 * sum(2 * it[j][0] + 1 for j in range(d)) + 6 * it[d][0] + 34 - 3 * d
    s = 12 + 3 * d
    for j in range(d):
        s += 3 * (2 * it[j][0] + 1)
        if j >= 1 and it[j][1] == 1:
            s += 4 if it[j][0] % 2 == 0 else 2
    return s
def reset_steps(it, i):
    return 28 - 3 * i + 3 * sum(2 * it[j][0] + 1 for j in range(i))
def cells_of(it):
    c=[0]
    for n,s in it: c+=[1,0]*n+([] if s=='E' else [s])
    return c
def parse(cells):
    i=1; items=[]
    assert cells[0]==0
    while i<len(cells):
        n=0
        while cells[i:i+2]==[1,0]: n+=1; i+=2
        if i>=len(cells): items.append((n,'E')); break
        items.append((n,cells[i])); i+=1
    return items
def cell_sweep(it):
    c=cells_of(it)
    tape=bytearray(len(c)+40); off=20
    tape[off:off+len(c)]=bytes(c)
    pos=off-1; st=3; lo=pos; n=0
    while True:
        tr=TAB[(st,tape[pos])]
        if tr is None: return 'HALT',n
        tape[pos]=tr[0]; pos+=tr[1]; st=tr[2]; n+=1
        if pos<0 or pos>=len(tape)-1: raise RuntimeError('tape')
        if pos<lo:
            lo=pos
            if st==3 and tape[pos]==0:
                hi=len(tape)-1
                while hi>pos and tape[hi]==0: hi-=1
                return parse(list(tape[pos+1:hi+1])), n

def check_random(trials=40000, seed=1):
    import random
    random.seed(seed)
    tot = 0
    for _ in range(trials):
        k = random.randint(1, 5)
        it = [(random.randint(1, 12), 0)] + [(random.choice([0, 1, 2, 3, random.randint(0, 12)]), random.choice([0, 0, 1]))
                                            for _ in range(k)] + [(random.choice([0, 1, 2, 3, random.randint(0, 12)]), 1)]
        it = parse(cells_of(it))
        r = model(it)
        if not r:
            continue
        new, n = cell_sweep(it)
        assert new == r[0] and n == model_steps(it, r[1]), (it, r, new, n)
        tot += 1
    return tot


def check_blank(max_steps=3000000):
    """Every sweep start (D on a new leftmost cell) of a direct run against the model."""
    tape = bytearray(1 << 16); off = 1 << 15; pos = off; st = 0; lo = pos; t = 0
    it = None; T = None; k = 0
    while t < max_steps:
        tr = TAB[(st, tape[pos])]
        tape[pos] = tr[0]; pos += tr[1]; st = tr[2]; t += 1
        if pos < lo:
            lo = pos
            if st == 3 and tape[pos] == 0:
                hi = len(tape) - 1
                while tape[hi] == 0: hi -= 1
                cells = list(tape[pos + 1:hi + 1])
                if it is None:
                    it, T = parse(cells), t
                else:
                    r = model(it)
                    if r:
                        T += model_steps(it, r[1]); it = r[0]
                    else:
                        it, n = cell_sweep(it); T += n
                    assert cells_of(it) == cells and T == t, (k, t)
                k += 1
    return k


if __name__ == "__main__":
    if sys.argv[1:2] == ["check"]:
        print("random sweeps checked:", check_random())
        print("sweep starts from blank checked:", check_blank())
