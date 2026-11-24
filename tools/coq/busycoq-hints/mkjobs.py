import json,sys
from words import cand, variants
fam=json.load(open('/mnt/project-files/plan/families.json'))
order=sys.argv[1].split(',')
seen=set(); jobs=[]
allm=[l.split()[1] for l in open('/mnt/project-files/BB6_holdouts_608.txt') if l.strip()]
groups=[(f,fam[f]['machines']) for f in order if f in fam]
if 'ALL' in order: groups.append(('ALL',allm))
for f,ms in groups:
    for m in ms:
        if m in seen: continue
        seen.add(m)
        ws,h=cand(m)
        if h: print('HALTS?',m,file=sys.stderr); continue
        tag=lambda k: ','.join(''.join(map(str,w)) for w in variants(ws[:k]))
        cfgs={'def':'','rep3':'--repeaters '+tag(3),'rep6x':'--repeaters '+tag(6)+' --mnc 4 --exploop',
              'rep4a':'--repeaters '+tag(4)+' --arithseq'}
        if ws: cfgs['bs%d'%len(ws[0])]='--block-size %d --arithseq'%len(ws[0])
        for k,a in cfgs.items(): jobs.append(f"{f}\t{m}\t{k}\t{a}")
print('\n'.join(jobs))
