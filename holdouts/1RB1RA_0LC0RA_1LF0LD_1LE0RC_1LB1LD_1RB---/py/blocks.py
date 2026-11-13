"""Tape of 1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB--- as lengths of blocks of ones (zN = N zeros in a row where N > 1 or at an end), repeated words
bracketed.  usage: c/dump MAXSTEPS > d.txt ; python3 holdouts/1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---/py/blocks.py d.txt"""
import sys,re
def blocks(s):
    # tape string -> list of tokens: run lengths of ones; zeros runs >1 as 'z<k>'
    out=[]
    for m in re.finditer(r'1+|0+',s):
        g=m.group()
        if g[0]=='1': out.append(str(len(g)))
        elif len(g)>1 or m.start()==0 or m.end()==len(s): out.append('z%d'%len(g))
    return out
def comp(seq,maxw=40,minrep=3):
    out=[];i=0;n=len(seq)
    while i<n:
        best=None
        for w in range(1,maxw+1):
            if i+2*w>n:break
            k=1
            while seq[i+k*w:i+(k+1)*w]==seq[i:i+w]:k+=1
            if k>=minrep and (best is None or k*w>best[0]*best[1]): best=(k,w)
        if best:
            k,w=best; out.append('(%s)^%d'%(' '.join(seq[i:i+w]),k)); i+=k*w
        else: out.append(seq[i]); i+=1
    return ' '.join(out)
if __name__=='__main__':
    for line in open(sys.argv[1]):
        ev,k,lo,hi,s=line.split()
        print(ev,k,lo,hi,'|',comp(blocks(s)))
