import re,subprocess,os
HERE=os.path.dirname(os.path.abspath(__file__))
def digits(tape):
    """tape: cells left of head, left to right. returns list of digits reading from head leftwards, plus leftover"""
    t=tape
    if len(t)%2: t='0'+t
    pairs=[t[i:i+2] for i in range(len(t)-2,-2,-2)]
    d=[];run=0;bad=[]
    for i,p in enumerate(pairs):
        if p=='11': run+=1
        elif p=='01': d.append(run);run=0
        else: bad.append((i,p)); d.append(run); d.append('?'+p); run=0
    d.append(run)
    return d
def from_digits(d):
    """digits (head-first) -> tape string (left to right)"""
    pairs=[]
    for i,x in enumerate(d):
        pairs+=['11']*x
        if i<len(d)-1: pairs.append('01')
    return ''.join(reversed(pairs))
def fmt(d):
    s=' '.join(map(str,d))+' '
    s=re.sub(r'((?:4 ){3,})',lambda m:'4^%d '%(len(m.group(1))//2),s)
    s=re.sub(r'((?:0 3 ){3,})',lambda m:'(0 3)^%d '%(len(m.group(1))//4),s)
    return s.strip()
def sim(tape,maxsteps,vf=1,vt=0,ve=1):
    out=subprocess.run([os.path.join(HERE,'sim'),tape or '-',str(maxsteps),str(vf),str(vt),str(ve)],capture_output=True,text=True).stdout
    return [l.split() for l in out.splitlines()]
