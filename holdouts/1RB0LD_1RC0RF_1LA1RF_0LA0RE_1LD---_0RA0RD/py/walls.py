import sys, re
sys.path.insert(0,'/home/user/busy-beaver-explorer/tools/py')
from bbtools import symtm
from bbtools.symtm import Rep, Lin, Blank, Ctx, Config
from bbtools.machine import Machine, STATES
m=Machine.parse('1LB0RD_1LC0LF_1RA1LF_0RA0LE_1RD---_0LA0LD'); Q=3
RUN=(1,0,0,0)
def sample(c):
    if c.steps.is_zero() or c.state!=Q: return False
    r=symtm.canon(c.right)
    return (r==[Blank()] or r==[0,Blank()]) and c.left[-3:]==[1,0,0]
def conc(toks,env):
    out=''
    for t in toks:
        if isinstance(t,int): out+=str(t)
        elif isinstance(t,Rep): out+=''.join(map(str,t.word))*t.n.subs(env)
        elif isinstance(t,Blank): out+='B'
        elif isinstance(t,Ctx): out+='~'
    return out
NAMES={(1,1,1,1,1,1):'Z'}
def digits(cells):
    # cells without prefix marker; parse blocks -> digit string
    bl=[(len(a),len(z)) for a,z in re.findall(r'(1+)(0+)',cells)]
    out=[];k=0;i=0
    while i<len(bl):
        x=bl[i]
        if x==(1,3): k+=1;i+=1;continue
        if bl[i:i+3]==[(1,1)]*3: out.append('[%d]Z'%k); i+=3
        elif x==(1,1): out.append('[%d]O'%k); i+=1
        elif x==(1,5): out.append('[%d]T'%k); i+=1
        else: out.append('[%d]b%d_%d'%((k,)+x)); i+=1
        k=0
    return ' '.join(out)+' [%d]'%k
def rule(pre,w):
    left=[pre]+w+[Rep(RUN,Lin('L')+1)]+[1,0,0]
    c=Config(left,Q,[Blank()])
    try:
        c=symtm.run(m,c,sample,max_moves=20000,rotate=True)
    except symtm.TouchContext: return 'touches context'
    except symtm.Halted: return 'HALT'
    except Exception as e: return type(e).__name__
    s=conc(c.left,{'L':9,'a':19})
    mk=s[0]; body=s[1:]
    # strip trailing '100' end
    if mk=='~' and not body.startswith('1'): body=body.lstrip('0') and body[body.index('1'):]
    return ('^' if mk=='B' else '..')+digits(body[:-3]).replace('[10]','[L+1]').replace('[9]','[L]').replace('[20]','[a+1]').replace('[19]','[a]').replace('[18]','[a-1]').replace('[21]','[a+2]').replace('[30]','[a+L+2]').replace('[29]','[a+L+1]').replace('[31]','[a+L+3]')
lit=lambda s:[int(c) for c in s]
print('wall | at the tape end | after a run of a+1 blocks')
for a in range(1,5):
    for b in range(1,10):
        w=lit('1'*a+'0'*b)
        r1=rule(Blank(),w)
        r2=rule(Ctx('L'),[Rep(RUN,Lin('a')+1)]+w)
        print('b%d_%d | %s | %s'%(a,b,r1,r2))
for nm,ws in (('Z','101010'),('O O','1010'),('Z O','10101010'),('T O','10000010'),('O Z','10101010')):
    print(nm,'|',rule(Blank(),lit(ws)),'|',rule(Ctx('L'),[Rep(RUN,Lin('a')+1)]+lit(ws)))
