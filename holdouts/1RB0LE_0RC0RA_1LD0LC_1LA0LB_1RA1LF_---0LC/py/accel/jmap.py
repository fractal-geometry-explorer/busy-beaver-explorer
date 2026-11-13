from sim import *
B="111111111010"
def snapshot_template(L, P_len, j):
    """run one event of L (odd, m=1) until head arrives at first cell of block j (from right) in state C; return tape cells
    right of that position within block j (the 'arrival context')."""
    pass
def jump(P, ctx_right, nb=2, maxt=10**7):
    """tape = P + B*nb + ctx_right (cells of the arrival block, head on its first cell in state C).
    run until head moves right past the end of the region; return (P', state, rest)"""
    s=P+B*nb+ctx_right
    off=50; N=len(s)+100
    tape=bytearray(N)
    for i,c in enumerate(s): tape[off+i]=int(c)
    pos=off+len(P)+12*nb; st=2  # C
    end=off+len(s); left=off
    t=0
    while t<maxt:
        r=tape[pos]; tr=T[(st,r)]
        if tr is None: return ('HALT',t,pos-left)
        w,d,ns=tr; tape[pos]=w; pos+=d; st=ns; t+=1
        if pos<off-40: return ('LEFT',)
        if pos>=end: 
            out=bytes(tape[off-40:end]).translate(bytes.maketrans(b'\x00\x01',b'01')).decode()
            return ('OUT',"ABCDEF"[st],out,t)
    return ('MAXT',)
