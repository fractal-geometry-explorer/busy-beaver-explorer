"""For each base macro rule of busycoq PR 93 (T3 = W on these traces), simulate W from the rule's left-hand side
with the context cells unknown ('U') and report every D-reads-0 step whose left neighbour is 1 (M halts) or unknown
(M's behaviour depends on the context).  W frame: W = 1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB0LF.
Notation as busycoq: l <* w pushes w with hd w next to the head; CfgR l r = l A> 0100 r; CfgL l r = l <B 1 r;
CfgJ l r = l <C 100 r (head on hd l)."""
import itertools, sys
W='1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB0LF'
T={}
for q,part in enumerate(W.split('_')):
    for b in (0,1):
        t=part[3*b:3*b+3]; T[(q,b)]=(int(t[0]),1 if t[1]=='R' else -1,'ABCDEF'.index(t[2]))
def P(w,n): return w*n
def Dw(n): return [1]+[1,1]*n+[0,0]
def Sw(n): return [1]+[0,1]*(1+n)
def PL(n): return P([1,0],n+4)+P([1,1],n)+Sw(0)+Sw(0)
def DEF(a,k): return P([1,0],a)+P([1],k)+[0,1]+Sw(0)
def Lw(*ws, base='U'):
    """l <* w1 <* w2 ... : outward = wk ++ ... ++ w1"""
    out=[]
    for w in reversed(ws): out+=w
    return out, base
def Rw(*ws, base='U'):
    out=[]
    for w in ws: out+=w
    return out, base
def cfg(mode,L,R):
    """returns (state, head index in tape, tape dict, known range) with left outward list L=(cells,base)"""
    lc,lb=L; rc,rb=R
    if mode=='R': st='A'; headR=[0,1,0,0]+rc; left=lc
    elif mode=='L': st='B'; headR=None
    elif mode=='J': st='C'; headR=None
    if mode=='R':
        tape={}; 
        for i,x in enumerate(left): tape[-1-i]=x
        for i,x in enumerate(headR): tape[i]=x
        lo=-len(left); hi=len(headR)-1; pos=0
    else:
        pre=[1] if mode=='L' else [1,0,0]
        tape={}
        for i,x in enumerate(lc): tape[-i]=x       # head on hd l at position 0
        for i,x in enumerate(pre+rc): tape[1+i]=x
        lo=-(len(lc)-1); hi=len(pre+rc); pos=0
    return 'ABCDEF'.index(st),pos,tape,lo,hi,lb,rb
def run(mode,L,R,limit=200000):
    q,pos,tape,lo,hi,lb,rb=cfg(mode,L,R)
    def get(p):
        if p in tape: return tape[p]
        if p<lo: return 0 if lb=='0' else 'U'
        if p>hi: return 0 if rb=='0' else 'U'
        return tape.get(p,0)
    ev=[]; steps=0
    while steps<limit:
        b=get(pos)
        if b=='U': return ev,steps,'context'
        if q==3 and b==0:
            lft=get(pos-1)
            if lft!=0: ev.append((steps,lft))
        w,d,q2=T[(q,b)]; tape[pos]=w; pos+=d; q=q2; steps+=1
    return ev,steps,'limit'
X=[0,1,2,3,5]
rules = {
 'rule_right':      lambda n: ('R', Lw(), Rw(Dw(n))),
 'rule_left':       lambda n: ('L', Lw(Sw(n)), Rw()),
 'rule_blank':      lambda : ('R', Lw(), Rw([0,0,0])),
 'rule_even':       lambda n: ('R', Lw(), Rw(P([1,1],1+n),[0,0])),
 'rule_restart':    lambda b: ('L', Lw([1,1,1],P([1,0],1+b)), Rw()),
 'rule_overflow2':  lambda b: ('L', Lw([1,1],P([1,0],1+b),base='0'), Rw()),
 'rule_overflow1':  lambda b,n: ('L', Lw([1],P([1,0],1+b),base='0'), Rw(Dw(n))),
 'rule_collision':  lambda : ('L', Lw([0,0,1,1,0,1]), Rw()),
 'rule_leftJ':      lambda n: ('J', Lw(Sw(n)), Rw()),
 'rule_turnB':      lambda n: ('L', Lw([1,1]), Rw(Dw(n))),
 'rule_turnJ':      lambda b: ('J', Lw([1,1,1],P([1,0],b)), Rw()),
 'rule_finishP':    lambda b: ('L', Lw(Sw(0),[0,1],P([1,0],1+b)), Rw()),
 'rule_defect0':    lambda m: ('R', Lw(), Rw([1,0],Dw(0),[1],P([1,1],m),[0])),
 'rule_defect1':    lambda m: ('R', Lw(), Rw([1,0],Dw(1),[1],P([1,1],m),[0])),
 'rule_defect2':    lambda n,m: ('R', Lw(), Rw([1,0],Dw(2+n),[1],P([1,1],m),[0])),
 'rule_defect_blank0': lambda : ('R', Lw(), Rw([1,0],Dw(0),[0,0])),
 'rule_defect_blankS': lambda n: ('R', Lw(), Rw([1,0],Dw(1+n),[0,0])),
 'rule_paired':     lambda k,n: ('R', Lw(), Rw(P([1,0],k*2),Dw(n))),
 'rule_emptyR':     lambda : ('R', Lw(), Rw(base='0')),
 'rule_collide':    lambda : ('R', Lw(), Rw([1,0],Dw(0),Dw(0))),
 'rule_pairR':      lambda n: ('R', Lw(), Rw([1,0],Dw(2+n),Dw(2+n))),
 'rule_zeroL_DD':   lambda a,b: ('L', Lw(base='0'), Rw(Dw(a),Dw(b))),
 'rule_zeroL_D10_0':lambda : ('L', Lw(base='0'), Rw(Dw(0),[1,0])),
 'rule_zeroL_D10_S':lambda a: ('L', Lw(base='0'), Rw(Dw(1+a),[1,0])),
 'rule_zeroL_1':    lambda : ('L', Lw([1],base='0'), Rw()),
 'rule_zeroL_J_mid':lambda n: ('J', Lw(base='0'), Rw(Dw(n))),
 'def_k0_ML':       lambda a: ('L', Lw(DEF(a,0)), Rw()),
 'def_k1_ML':       lambda a: ('L', Lw(DEF(a,1)), Rw()),
 'def_k2_ML':       lambda a: ('L', Lw(DEF(a,2)), Rw()),
 'def_k1_MJ':       lambda a: ('J', Lw(DEF(a,1)), Rw()),
 'def_k2_MJ':       lambda a: ('J', Lw(DEF(a,2)), Rw()),
 'def_02_ML':       lambda dn: ('L', Lw(DEF(0,2)), Rw(Dw(dn))),
 'def_restart':     lambda a,k: ('L', Lw(DEF(a,k)), Rw()),
 'def_turnJ':       lambda a,k: ('J', Lw(DEF(a,k)), Rw()),
 'rule_mr_a0_DEF':  lambda la,lk,m: ('R', Lw(DEF(la,lk)), Rw([1,0],Dw(0),Dw(m))),
 'rule_mr_a0_S_DEF':lambda la,lk,sn,m: ('R', Lw(DEF(la,lk),Sw(sn)), Rw([1,0],Dw(0),Dw(m))),
 'rule_PL_L':       lambda n: ('L', Lw(PL(n)), Rw()),
 'rule_PL_J':       lambda n: ('J', Lw(PL(n)), Rw()),
}
import inspect
bad=0
for name,f in rules.items():
    k=len(inspect.signature(f).parameters)
    flagged=set(); ends=set()
    for args in itertools.product(X,repeat=k):
        if name.startswith('def_restart') or name.startswith('def_turnJ') or name.startswith('rule_mr_a0'):
            if args[1]<3: continue
        mode,L,R=f(*args)
        ev,steps,end=run(mode,L,R)
        ends.add(end)
        for s,v in ev: flagged.add((args,v,s))
    if flagged:
        bad+=1
        ex=sorted(flagged)[:6]
        print(f'{name}: {len(flagged)} D0 events with left != 0, e.g. {ex}')
    else: print(f'{name}: clean ({",".join(sorted(ends))})')
print('flagged rules:',bad)

def runraw(q,pos_on_left,L,R,limit=200000):
    """raw configuration: state q; if pos_on_left the head is on hd of L (outward list), else on hd of R"""
    lc,lb=L; rc,rb=R; tape={}
    if pos_on_left:
        for i,x in enumerate(lc): tape[-i]=x
        for i,x in enumerate(rc): tape[1+i]=x
        lo=-(len(lc)-1); hi=len(rc)
    else:
        for i,x in enumerate(lc): tape[-1-i]=x
        for i,x in enumerate(rc): tape[i]=x
        lo=-len(lc); hi=len(rc)-1
    pos=0; q='ABCDEF'.index(q)
    def get(p):
        if p in tape: return tape[p]
        if p<lo: return 0 if lb=='0' else 'U'
        if p>hi: return 0 if rb=='0' else 'U'
        return 0
    ev=[]; steps=0
    while steps<limit:
        b=get(pos)
        if b=='U': return ev,steps,'context'
        if q==3 and b==0 and get(pos-1)!=0: ev.append((steps,get(pos-1)))
        w,d,q2=T[(q,b)]; tape[pos]=w; pos+=d; q=q2; steps+=1
    return ev,steps,'limit'
if __name__=='__main__':
    scans={'scanR':lambda n:('A',False,Lw(),Rw([0,1],P([1,1],n))),
           'scanR1':lambda n:('A',False,Lw(),Rw([0,1,1],P([1,1],n))),
           'scanPair':lambda n:('A',False,Lw(),Rw([0,1],P([0,1,0,1],n))),
           'scanB':lambda n:('B',True,Lw(P([0,1],n)),Rw()),
           'scanB0':lambda n:('B',True,Lw([0],P([1,0],n),base='0'),Rw()),
           'scanC':lambda n:('C',True,Lw(P([1,0],n)),Rw()),
           'ones':lambda n:('A',False,Lw(),Rw(P([1],n)))}
    for name,f in scans.items():
        fl=[]
        for n in range(8):
            q,pl,L,R=f(n); ev,st,end=runraw(q,pl,L,R)
            if ev: fl.append((n,ev[:3]))
        print(name,'clean' if not fl else fl)
