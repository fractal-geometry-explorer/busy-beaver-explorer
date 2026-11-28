import json,re,os,sys
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__))); from trim import trim
V=os.environ.get('BUSYCOQ_VERIFY','busycoq/verify')
J=json.load(open('../../holdouts/busycoq_templates.json'))['transplants']
jobs=[r for r in J if r['outcome']=='goals left open']
seen=set(); out=[]
for r in jobs:
    key=(r['machine'],r['file'])
    if key in seen: continue
    seen.add(key)
    src=open(f"{V}/{r['id']}.v").read()
    h=r['machine'] if not r['mirror'] else r['machine'].replace('L','x').replace('R','L').replace('x','R')
    s=trim(src,h)
    i=s.index('"%s"'%h); q=s.index('Qed.',i)
    blk=s[i:q]
    m=re.search(r'eapply \((\w+)\.nonhalt',blk); mod=m.group(1)
    mm=re.search(r'Module %s\.(.*?)End %s\.'%(mod,mod),s,re.S).group(1)
    hyps=[x for x in re.findall(r'Hypothesis ([\w\']+)\s*:',mm) if x not in ('tm','init','Pinit')]
    hyps=[x for x in hyps if re.search(r'Hypothesis %s\s*:\s*\n?\s*forall'%re.escape(x),mm)]
    em=re.search(r'1-(\d+): es\.',blk); K=int(em.group(1))
    names=hyps[:K]+['?']*(K-len(hyps))
    probe=''.join(f'  first [ only 1: (es; fail); idtac "PROBE {n} proved" | idtac "PROBE {n} open"; cycle 1 ].\n' for n in names)
    probe+='  first [ only 1: (esx; fail); idtac "PROBE init proved" | idtac "PROBE init open"; cycle 1 ].\n'
    probe+='  first [ only 1: (cbn; lia); idtac "PROBE Pinit proved" | idtac "PROBE Pinit open"; cycle 1 ].\nAdmitted.\n'
    a=blk.index(em.group(0))
    nb=blk[:a]+probe.lstrip()
    s2=s[:i]+nb+s[q+4:]
    pid='TP'+r['id'][2:]
    open(f'{V}/{pid}.v','w').write(s2); out.append(pid)
open('probe_todo.txt','w').write('\n'.join(out)+'\n'); print(len(out))
