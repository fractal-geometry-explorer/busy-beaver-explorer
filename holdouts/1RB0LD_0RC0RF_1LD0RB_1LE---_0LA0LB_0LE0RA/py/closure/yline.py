"""Plain runs of the halting shape H and of the line Q = 3M - 1 of shape Y (mirrored tape, head F at the near end),
and the visits of Y in the accelerated run from blank tape.
usage: yline.py plain | yline.py run SECONDS   (run needs the environment of the README)"""
import os
import sys, collections
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..',
                                '1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD', 'py', 'closure'))

M='1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA'
def run_plain(tape, maxsteps):
    T = {}
    for i, s in enumerate(M.split('_')):
        for b in (0, 1):
            t = s[3 * b:3 * b + 3]
            T[(i, b)] = None if t[2] == '-' else (int(t[0]), -1 if t[1] == 'R' else 1, ord(t[2]) - 65)   # mirrored
    tp = {i: int(ch) for i, ch in enumerate(tape)}
    h, q, n = 0, 5, 0
    while n < maxsteps:
        t = T[(q, tp.get(h, 0))]
        if t is None: return 'halts after %d steps' % n
        tp[h] = t[0]; h += t[1]; q = t[2]; n += 1
    return 'no halt in %d steps' % n
Y=lambda P,Mm,Q:'00001101'+'1000'*P+'1011'+'1000'*Mm+'1010100001'+'1000'*Q+'101000000101'
if sys.argv[1]=='plain':
    for P in (21,23,31): print('H P=%d'%P, run_plain('00001101'+'1000'*P+'101110110100001101',10**7))
    for P,Mm in ((21,3),(21,8),(23,8),(33,12),(21,22)):
        for dq in (0,-2,2,1):
            Q=3*Mm-1+dq
            print('Y P=%d M=%d Q=3M-1%+d:'%(P,Mm,dq), run_plain(Y(P,Mm,Q), 3*10**7 if dq==0 else 3*10**6))
else:
    import pclosure
    res=pclosure.real_nodes(float(sys.argv[2]))
    print(len(res),'nodes, last step digits',len(str(res[-1][0])))
    sh='00001101 (1000)^n 1011 (1000)^n 1010100001 (1000)^n 101000000101'
    v=[cs for st,t,cs in res if t==sh]
    ds=[q-3*m+1 for p,m,q in v]
    print('Y visits',len(v),'min |Q-3M+1|',min(map(abs,ds)) if ds else None, 'D mod 2',collections.Counter(d%2 for d in ds),'D mod 3',collections.Counter(d%3 for d in ds), 'D mod 4',collections.Counter(d%4 for d in ds))
    print('H visits',sum(1 for st,t,cs in res if t=='00001101 (1000)^n 101110110100001101'))
