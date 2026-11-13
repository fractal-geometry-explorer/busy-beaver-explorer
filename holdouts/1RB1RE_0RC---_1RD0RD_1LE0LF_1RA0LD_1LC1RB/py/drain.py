"""The drain machine of 1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB: an exact macro simulator.

Macro configurations (cells; the left of the tape is blank):
    D(A,B)  1^A (01)^B 0 C> 0 Z        the drain; S = D(1,0) = `1 0 C> 0` is the start (step 2 from blank tape)
    P(A,B)  1^A (01)^B 1 1 1 0 C> 0 Z  the parity tail
    T(n)    E> (01)^n Z                the head at the left end
The environment Z (everything right of the head cell, or right of the pairs for T) is a list of blocks (g,c) =
`0^g (10)^c 1`, then blank tape.  `step` applies one of the rules proved in lean/Macro.lean and lean/Halt.lean
(several sweeps at once), with the exact step count; the few small cases no rule covers go to `nxt`, which runs the
machine cell by cell to the next macro configuration.  `check` compares the macro run with a plain run, cell for
cell, at every macro configuration.

usage (from the repository root):
    python3 holdouts/1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB/py/drain.py check 5e6     # against the plain run
    python3 holdouts/1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB/py/drain.py run 6e9       # the macro run, gaps made
    python3 holdouts/1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB/py/drain.py gaps 0 2500   # which gaps G halt
"""

import re,sys
M="1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB"
TR={}
for i,tr in enumerate(M.split('_')):
    for r in (0,1):
        t=tr[3*r:3*r+3]
        TR[(i,r)]=None if t[0]=='-' else (int(t[0]),1 if t[1]=='R' else -1,ord(t[2])-65)
def env_cells(env):
    s=''
    for g,c in env: s+='0'*g+'10'*c+'1'
    return s
def build(cfg):
    act,env=cfg
    k=act[0]
    if k=='S': L='10'; st=2; R='0'
    elif k=='D': L='1'*act[1]+'01'*act[2]+'0'; st=2; R='0'
    elif k=='P': L='1'*act[1]+'01'*act[2]+'1110'; st=2; R='0'
    elif k=='T': L=''; st=4; R='01'*act[1]
    return L, R+env_cells(env), st
ENVRE=re.compile(r'(0*)((?:10)*?1)(?=$|1|00)')
def parse_env(s):
    s=s.rstrip('0'); env=[]; p=0
    while p<len(s):
        m=ENVRE.match(s,p)
        if not m: return None
        env.append((len(m.group(1)),(len(m.group(2))-1)//2)); p=m.end()
    return tuple(env)
DRE=re.compile(r'^(1*)((?:01)*)0$'); PRE=re.compile(r'^(1*)((?:01)*)1110$')
def parse(t,h,st,lo):
    """t list cells, h head; lo first index possibly nonzero. returns macro cfg or None"""
    if st==4:
        if any(t[lo:h]): return None
        s=''.join(map(str,t[h:]))
        m=re.match(r'(?:01)*',s); n=len(m.group(0))//2
        e=parse_env(s[m.end():])
        return (('T',n),e) if e is not None else None
    if st==2 and t[h]==0:
        L=''.join(map(str,t[lo:h])).lstrip('0')
        e=parse_env(''.join(map(str,t[h+1:])))
        if e is None: return None
        if L=='10': return (('S',),e)
        m=DRE.match(L)
        if m: return (('D',len(m.group(1)),len(m.group(2))//2),e)
        m=PRE.match(L)
        if m: return (('P',len(m.group(1)),len(m.group(2))//2),e)
    return None
def nxt(cfg,maxn=10**8,want=None):
    L,R,st=build(cfg)
    pad=64
    t=[0]*pad+[int(c) for c in L]+[int(c) for c in R]+[0]*pad
    h=pad+len(L); n=0; lo=pad
    while n<maxn:
        if h<2: t=[0]*pad+t; h+=pad; lo+=pad
        if h>=len(t)-2: t+=[0]*pad
        tr=TR[(st,t[h])]
        if tr is None: return n+1,'HALT',None
        w,d,q=tr; t[h]=w; h+=d; st=q; n+=1
        if h<lo: lo=h
        if st==4 or (st==2 and t[h]==0 and t[h-1]==0):
            c=parse(t,h,st,lo)
            if c is not None and (c[0][0]=='T' and c[0][1]>0 or c[0][0]!='T' and ( not c[1] or c[1][0][0]>=1)) and (want is None or c[0][0] in want): return n,'ok',c
    return n,'timeout',None
def show(c):
    if c is None: return '-'
    a,e=c
    return f"{a[0]}{a[1:]} env={list(e)}"


INF = None
def canon(env):
    out=[]
    for g,c in env:
        if out and g==1:
            pg,pc=out[-1]; out[-1]=(pg,pc+c+1)
        else: out.append((g,c))
    return out

class Fallback(Exception): pass

def step(act, env):
    """one macro move; returns (act, env, steps, kind) ; kind 'HALT' for halts"""
    k=act[0]
    z = env[0][0] if env else INF
    rest = env[1:]
    if k=='D':
        _,A,B=act
        if A>=3:
            if z is INF or z>=3:
                kk=(A-1)//2
                if z is not INF: kk=min(kk,(z-1)//2)
                # steps of sweeps: sum_{i<kk} (6*(B+2i)+16)
                st=kk*(6*B+16)+6*kk*(kk-1)
                ne= env if z is INF else [(z-2*kk,env[0][1])]+rest
                return ('D',A-2*kk,B+2*kk),ne,st,'sweep'
            if z==2:
                c=env[0][1]
                if not rest or rest[0][0]>=1:
                    ne=([(rest[0][0]-1,rest[0][1])]+rest[1:]) if rest else []
                    return ('D',A-2,B+c+3),canon(ne) if ne and ne[0][0]>=1 else ne,6*B+4*c+20,'absorb'
                raise Fallback
            if z==1:
                c=env[0][1]
                if c>=2:
                    kk=min((A-1)//2,c//2)
                    st=kk*(6*B+24)+9*kk*(kk-1)
                    return ('D',A-2*kk,B+3*kk),[(1,c-2*kk)]+rest,st,'odd'
                if c==1:
                    if not rest or rest[0][0]>=1:
                        return ('D',A-2,B+3),(rest if rest else []),6*B+24,'odd_end1'
                    raise Fallback
                if c==0:
                    if not rest or rest[0][0]>=5:
                        ne=[(rest[0][0]-5,rest[0][1])]+rest[1:] if rest else []
                        return ('P',A-2,B+3),ne,6*B+23,'odd_end0'
                    if rest[0][0]==3: return None,None,6*B+22+1,'HALT'
                    raise Fallback
            raise Fallback
        if A in (0,1,2):
            if z is not INF and z<1: raise Fallback
            ne = [] if z is INF else [(z-1,env[0][1])]+rest
            if A==2:
                ne=canon([(1,B+1)]+ne)
                return ('D',1,0),ne,2*B+11,'end2'
            n=B+3 if A==1 else B+2
            st=2*B+6 if A==1 else 2*B+4
            return Tnorm(n,ne,st,'end%d'%A)
    if k=='T':
        n=act[1]
        if z is INF or z>=5:
            ne=[] if z is INF else [(z-4,env[0][1])]+rest
            return ('D',2*n+2,0),ne,2*n+3,'tblank'
        if z==0 and env[0][1]>=1 and n>=1:
            return ('D',2*n-1,0),[(1,env[0][1]-1)]+rest,2*n+4,'tseg'
        if z==2: return None,None,2*n+3,'HALT'
        raise Fallback
    if k=='P':
        _,A,B=act
        if B%2==0 and A>=2 and (z is INF or z>=5):
            ne=[] if z is INF else [(z-4,env[0][1])]+rest
            return ('D',A-1,B+4),ne,11*B+44,'peven'
        if B%2==1 and (z is INF or z>=3):
            ne=[(A+1,B+2)]+([] if z is INF else [(z-3,env[0][1])]+rest)
            return ('D',1,0),canon(ne),3*A+7*(B-1)+31,'podd'
        raise Fallback
    raise Fallback

def Tnorm(n,ne,st,kind):
    # T absorbs a first block with g==1
    while ne and ne[0][0]==1:
        n+=ne[0][1]+1; ne=ne[1:]
    return ('T',n),ne,st,kind

def slow(act,env):
    c=(tuple(act),tuple(env))
    if act[0]=='D' and act[1]==1 and act[2]==0: c=(('S',),tuple(env)) if False else c
    n,r,c2=nxt(c)
    if r=='HALT': return None,None,n,'HALT'
    if c2 is None: raise RuntimeError('slow failed %s %s'%(c,r))
    a2,e2=c2
    if a2[0]=='S': a2=('D',1,0)
    if a2[0]=='T':
        return Tnorm(a2[1],list(e2),n,'slow')
    return a2,list(e2),n,'slow'

def mstep(act,env):
    try: return step(act,env)
    except Fallback: return slow(act,env)

def cells_of(act, env):
    a = act
    if a[0] == 'D': L = '1' * a[1] + '01' * a[2] + '0'; R = '0'; st = 2
    elif a[0] == 'P': L = '1' * a[1] + '01' * a[2] + '1110'; R = '0'; st = 2
    else: L = ''; R = '01' * a[1]; st = 4
    return L, R + env_cells(env), st


def macro_run(act, env, tot, until, stop_on_empty=False, log=None):
    """iterate mstep; returns (outcome, steps, act, env, counts)"""
    import collections
    cnt = collections.Counter()
    while tot < until:
        try:
            a2, e2, st, kd = step(act, env)
        except Fallback:
            a2, e2, st, kd = slow(act, env)
            cnt['fallback'] += 1
        cnt[kd] += 1
        tot += st
        if kd == 'HALT':
            return 'HALT', tot, act, env, cnt
        if log is not None:
            log(tot - st, act, env, kd, a2, e2)
        act, env = a2, e2
        if stop_on_empty and not env:
            return 'merged', tot, act, env, cnt
    return 'running', tot, act, env, cnt


def check(n):
    traj = [(2, ('D', 1, 0), [])]
    macro_run(('D', 1, 0), [], 2, n, log=lambda t, a, e, k, a2, e2: traj.append((None, a2, e2)))
    # recompute absolute step counts
    tot = 2; out = [traj[0]]; act, env = traj[0][1], traj[0][2]
    for _, a2, e2 in traj[1:]:
        try: _, _, st, _ = step(act, env)
        except Fallback: _, _, st, _ = slow(act, env)
        tot += st; out.append((tot, a2, e2)); act, env = a2, e2
    size = 1 << 20; t = [0] * size; h = size // 2; st = 0; k = 0; lo = h; bad = 0
    for (T_, a, e) in out:
        while k < T_:
            w, d, q = TR[(st, t[h])]; t[h] = w; h += d; st = q; k += 1
            lo = min(lo, h)
        L, R, s2 = cells_of(a, e)
        left = ''.join(map(str, t[lo:h])).lstrip('0'); right = ''.join(map(str, t[h:h + len(R) + 50])).rstrip('0')
        if left != L.lstrip('0') or right != R.rstrip('0') or s2 != st:
            bad += 1
    print(f'{len(out)} macro configurations up to step {out[-1][0]}, {bad} differ from the plain run')
    return bad


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'check':
        sys.exit(1 if check(float(sys.argv[2])) else 0)
    if cmd == 'run':
        def log(t, a, e, k, a2, e2):
            if a2 == ('D', 1, 0) and e2 and e2[0][0] >= 3:
                print(f'step {t}: a gap of {e2[0][0]} zeros, made from {a[0]}{a[1:]}; environment {e2[:4]}', flush=True)
        r = macro_run(('D', 1, 0), [], 2, float(sys.argv[2]), log=log)
        print(r[0], 'at step', r[1], 'in', r[2], 'environment', r[3][:6], dict(r[4]))
    if cmd == 'gaps':
        for G in range(int(sys.argv[2]), int(sys.argv[3]) + 1):
            r = macro_run(('D', 1, 0), [(G, 3)], 0, 1e30, stop_on_empty=True)
            if r[0] == 'HALT':
                print(f'gap {G}: halts after {r[1]} steps, in {r[2]} with environment {r[3][:3]}', flush=True)
