import json,collections,re
from an import rows
d=json.load(open('pool_raw.json')); dec=json.load(open('../dec.json'))
info={m:(never,{k:(c,la) for k,c,la in stopped}) for m,T,st,never,stopped,u in rows}
L='ABCDEF'
def slots(m): return [m[i*7+b*3:i*7+b*3+3] for i in range(6) for b in range(2)]
cur=None; res=collections.defaultdict(dict)
for l in open('m1.txt'):
    p=l.split()
    if len(p)==2: cur=p[0]; continue
    if len(p)<5: continue
    P,mir,perm,nd=p[0],int(p[1][4:]),p[2][5:],int(p[3][3:])
    if nd==0: continue
    # which H slots differ: map H slot k -> P slot perm[k//2]*2+k%2
    hs=slots(cur); ps=slots(P); dif=[]
    for k in range(12):
        x=hs[k]
        if x!='---':
            dr=x[1]
            if mir: dr='L' if dr=='R' else 'R'
            x=x[0]+dr+L[int(perm[L.index(x[2])])]
        if ps[int(perm[k//2])*2+k%2]!=x: dif.append(k)
    never,quiet=info[cur]
    if all(k in never for k in dif): continue      # only the halting slot differs: says nothing
    src=[f for f in d['busycoq'].get(P,[]) if not f.startswith('Eqv')]+(['DM'] if P in d['dm'] else [])+(['OURS:'+dec[P]] if dec.get(P,'open')!='open' else [])
    res[cur][P]=(tuple(dif),perm[0]=='0',mir,perm,src)
out=[]
for h,v in sorted(res.items()):
    never,quiet=info[h]
    q=', '.join(f"{L[k//2]}{k%2}: {c} uses, last before {la:.3g}" for k,(c,la) in sorted(quiet.items()))
    srcs=collections.Counter(re.sub(r'\d*\.v$','',s) for x in v.values() for s in x[4])
    print(h,'|',q,'|',len(v),'proved tables agree on the rest:',dict(srcs.most_common(4)))
    out.append({'holdout':h,'quiet':{L[k//2]+str(k%2):{'uses':c,'last_use_before':la} for k,(c,la) in quiet.items()},'proved_tables_agreeing_elsewhere':[{'table':P,'start_kept':x[1],'mirror':x[2],'states':x[3],'proof':x[4]} for P,x in sorted(v.items())]})
json.dump(out,open('quiet_matches.json','w'),indent=0)
print(len(res),'holdouts;',sum(len(v) for v in res.values()),'pairs')
