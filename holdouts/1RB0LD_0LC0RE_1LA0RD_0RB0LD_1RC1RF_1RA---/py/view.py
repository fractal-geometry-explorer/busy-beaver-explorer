# tape views used in the README: pairs(left) writes the left part in 2-cell symbols (00 . 10 x 01 y 11 #), rtrip(right) the right part in 3-cell digits (001 0, 011 1, 010 2, 110 A, 101 B, 100 C, 111 D)
import sys
def pairs(l):
    ch=[]; s=l
    while len(s)>=2: ch.append(s[-2:]); s=s[:-2]
    if s: ch.append(s)
    m={'00':'.','10':'x','01':'y','11':'#','0':'0','1':'1'}
    return ''.join(m[c] for c in ch[::-1])
def rtrip(r):
    m={'001':'0','011':'1','010':'2','110':'A','101':'B','100':'C','111':'D','000':'_'}
    out=[r[:3]]+[r[j:j+3] for j in range(3,len(r),3)]
    return out[0]+' '+''.join(m.get(x,'('+x+')') for x in out[1:])
def fmt(line):
    c,t,lo,l,_,r=line.split()
    return '%s %s %s %s | %s'%(c,t,lo,pairs(l),rtrip(r))
if __name__=="__main__":
    a,b=int(sys.argv[1]),int(sys.argv[2]); every=int(sys.argv[3]) if len(sys.argv)>3 else 1
    for i,line in enumerate(open('sys.argv[4] if len(sys.argv)>4 else 'events.txt'')):
        t=int(line.split()[1])
        if a<=t<=b and i%every==0: print(fmt(line))
        if t>b: break
