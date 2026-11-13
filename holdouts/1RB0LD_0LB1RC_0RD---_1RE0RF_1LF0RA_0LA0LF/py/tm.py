import sys
def parse(m):
    T={}
    for i,s in enumerate(m.split('_')):
        for b in (0,1):
            t=s[3*b:3*b+3]
            T[(i,b)]=None if t[2]=='-' else (int(t[0]),1 if t[1]=='R' else -1,ord(t[2])-65)
    return T
def run_word(T,st,word,pos,maxs=10000):
    # run on finite word, head at pos; stop when leaving word; return (state,side,word,steps)
    w=list(word);n=0
    while 0<=pos<len(w):
        t=T[(st,w[pos])]
        if t is None: return ('H',pos,''.join(map(str,w)),n)
        w[pos]=t[0];pos+=t[1];st=t[2];n+=1
        if n>maxs: return ('loop',)
    return (chr(65+st),'L' if pos<0 else 'R',''.join(map(str,w)),n)
def sim(T,steps,show=None):
    tape={};pos=0;st=0;n=0
    while n<steps:
        b=tape.get(pos,0);t=T[(st,b)]
        if show and n in show:
            lo=min(tape) if tape else 0;hi=max(tape) if tape else 0
            s=''.join(('['+chr(65+st)+']' if p==pos else '')+str(tape.get(p,0)) for p in range(min(lo,pos),max(hi,pos)+1))
            print(n,s)
        if t is None: return ('halt',n)
        tape[pos]=t[0];pos+=t[1];st=t[2];n+=1
    return tape,pos,st
