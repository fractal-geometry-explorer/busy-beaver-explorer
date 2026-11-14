#!/usr/bin/env python3
"""Write lean/Visit.lean: the two-form visit law of a machine of the 1RB0LB_0RC0LE table family, by symbolic execution.

A visit: the head stands on a 0 (the lead cell) with a 0 on its left and a stream s on its right, in state C (form V)
or F (form W); it comes back in state A two cells further left, the two 0s restored and s rewritten.  Each rule is
found by running the table on a finite prefix of s; a nested visit (C or F arriving on a lead 0 with a 0 on its left
and the unread rest on its right) is taken from the hypotheses.

usage: visit2.py MACHINE NAMESPACE OUT.lean"""
import sys
def parse(s):
    tm={}
    for qi,q in enumerate(s.split('_')):
        for c,i in ((0,0),(1,3)):
            t=q[i:i+3]
            tm[(qi,c)]=None if t[0]=='-' else (int(t[0]), t[1], ord(t[2])-65)
    return tm
MAXP=4
FORMS={'V':2,'W':5}
FORM_OF={2:'V',5:'W'}
B=lambda b: 'true' if b else 'false'
def tape(cells, base):
    r=base
    for c in reversed(cells): r='cons %s (%s)'%(c if isinstance(c,str) else B(c), r)
    return r
def rule(tm, form, prefix):
    """symbolic visit of the given form on prefix ++ s."""
    left=[0,'x']; right=[0]+list(prefix); st=FORMS[form]; nsub=0; segs=[]; n=0; start=(list(left),list(right),st,0)
    subs=[]
    while True:
        if n>0 and st in FORM_OF and left and left[0]==0 and right==[0]:
            segs.append((start,n,(list(left),list(right),st,nsub)))
            if len(left)<2: return None
            b=left[1]; rest=left[2:]
            subs.append((FORM_OF[st],b,list(rest)))
            nsub+=1
            left=rest; right=[b,0,0]; st=0; n=0; start=(list(left),list(right),st,nsub)
            continue
        if not right: return None   # reads past the prefix
        c=right[0]
        if c=='x': return None
        t=tm[(st,c)]
        if t is None: return ('halt', start, n, (list(left),list(right),st,nsub), segs, subs)
        w,d,ns=t
        if d=='R': left=[w]+left; right=right[1:]
        else:
            if not left: return None
            right=[left[0],w]+right[1:]; left=left[1:]
        st=ns; n+=1
        if not left and st==0 and right[0]=='x' and right[1:3]==[0,0]:
            segs.append((start,n,(list(left),list(right),st,nsub)))
            return ('ok', segs, subs, right[3:], nsub)
        if n>400: return None
def top(tm, m):
    out=[]
    Z=8
    left=[0]*Z; right=[1,0,0]; st=0; n=0
    def step():
        nonlocal left,right,st,n
        c=right[0]; w,d,ns=tm[(st,c)]
        if d=='R': left=[w]+left; right=right[1:]
        else: right=[left[0],w]+right[1:]; left=left[1:]
        st=ns; n+=1
    while not (st==2 and left[0]==0 and right==[0,1,0]): step()
    n0=n; l0=list(left); b=left[1]; rest=left[2:]
    left=rest; right=[b,0,0]; st=0; n=0
    while not (st==0 and right==[1,0,0]): step()
    n1=n; l1=list(left)
    used=Z-len(l1)
    assert all(c==0 for c in l1)
    zl=lambda cells: tape(cells[:len(cells)-(Z-used)],'L')
    S='cons true (cons false (cons false s))'; S1="cons true (cons false (cons false s'))"
    out.append('/-- The configuration `0^∞ A> 1 0 0 s`. -/\ndef LE (s : Tape) : Config := ⟨blank, %s, .A⟩\n'%S)
    out.append("/-- A round, with any left tape that starts with %d blank cells. -/"%used)
    out.append("theorem round_gen {s s' : Tape} (h : V (cons true (cons false s)) s') (L : Tape) :\n    ∃ n, steps n ⟨%s, %s, .A⟩ = some ⟨L, %s, .A⟩ := by"%(tape([0]*used,'L'),S,S1))
    out.append('  obtain ⟨n1, e1⟩ := h (%s) (%s)'%(B(b), zl(rest)))
    out.append('  have a0 : steps %d ⟨%s, %s, .A⟩ = some ⟨%s, cons false (cons true (cons false s)), .C⟩ := rfl'%(n0,tape([0]*used,'L'),S,zl(l0)))
    out.append("  have a1 : steps %d ⟨%s, %s, .A⟩ = some ⟨L, %s, .A⟩ := rfl"%(n1,zl(rest),tape([b,0,0],"s'"),S1))
    out.append('  exact ⟨%d + n1 + %d, steps_seq trans (steps_seq trans a0 e1) a1⟩\n'%(n0,n1))
    out.append("theorem blank_eq : %s = blank := by\n  simp [cons_false_blank]\n"%tape([0]*used,'blank'))
    out.append("/-- A round: `0^∞ A> 1 0 0 s` becomes `0^∞ A> 1 0 0 s'` when a visit (form V) turns `1 0 s` into `s'`. -/")
    out.append("theorem round {s s' : Tape} (h : V (cons true (cons false s)) s') : ∃ n, steps n (LE s) = some (LE s') := by\n  obtain ⟨n, e⟩ := round_gen h blank\n  rw [blank_eq] at e\n  exact ⟨n, e⟩\n")
    out.append("/-- A round whose visit halts: the machine halts. -/")
    out.append("theorem round_halts {s : Tape} (h : VH (cons true (cons false s))) : TM.Halts trans (LE s) := by")
    out.append('  obtain ⟨m, c, e, hc⟩ := h (%s) (%s)'%(B(b), zl(rest).replace('L','blank')))
    out.append('  have a0 : steps %d ⟨%s, %s, .A⟩ = some ⟨%s, cons false (cons true (cons false s)), .C⟩ := rfl'%(n0,tape([0]*used,'blank'),S,zl(l0).replace('L','blank')))
    out.append('  rw [blank_eq] at a0')
    out.append('  exact ⟨%d + m, c, steps_seq trans a0 e, hc⟩\n'%n0)
    # start: emulate the list simulator of tools/lean/TM/Fin.lean
    l=[]; r=[]; st=0; k=0
    while True:
        c=r[0] if r else 0
        w,d,ns=tm[(st,c)]
        if d=='R': l=[w]+l; r=r[1:]
        else: r=[(l[0] if l else 0), w]+r[1:]; l=l[1:]
        st=ns; k+=1
        if st==0 and r[:3]==[1,0,0] and not any(l) and k>1: break
    s0=r[3:]
    bl=lambda cs: '['+', '.join(B(c) for c in cs)+']'
    out.append("/-- From blank tape the machine reaches `0^∞ A> 1 0 0 %s 0^∞` after %d steps. -/"%(''.join(map(str,s0)),k))
    out.append("theorem start : steps %d init = some (LE (app %s blank)) := by"%(k,bl(s0)))
    out.append("  have h := blank_reaches trans (q := St.A) (n := %d) (c := ⟨%s, %s, .A⟩) (by decide)"%(k,bl(l),bl(r)))
    out.append("  simpa [LE, FCfg.toCfg, cons_false_blank] using h\n")
    return out, s0, k
def svar(i,k):
    return 's' if i==0 else ("s'" if i==k else 's%d'%i)
def cfg(c, k, Lname='L'):
    left,right,st,i=c
    return '⟨%s, %s, .%s⟩'%(tape(left,Lname), tape(right, svar(i,k)), 'ABCDEF'[st])
def lean(name, m):
    tm=parse(m); out=[]; found=[]
    out.append('import Machine\n')
    out.append('/-! The two-form visit law of %s, generated by `py/visit2.py`; do not edit by hand.\n\nA visit: the head stands on a 0 (the lead cell) with a 0 on its left and a stream `s` on its right, in state C\n(`V s s\'`) or in state F (`W s s\'`); it comes back in state A two cells further left, both 0s restored and `s`\nrewritten to `s\'`.  `VH s`, `WH s`: the visit halts instead.  The rules below are for every stream, every cell `x`\nand every left tape `L`. -/\n'%m)
    out.append('namespace %s\n\nopen TM\n'%name)
    for f,q in (('V','C'),('W','F')):
        out.append("/-- One visit entered in state %s rewrites the stream `s` to `s'`. -/\ndef %s (s s' : Tape) : Prop :=\n  ∀ (x : Bool) (L : Tape), ∃ n, steps n ⟨cons false (cons x L), cons false s, .%s⟩ = some ⟨L, cons x (cons false (cons false s')), .A⟩\n"%(q,f,q))
        out.append("/-- A visit entered in state %s to the stream `s` halts the machine. -/\ndef %sH (s : Tape) : Prop :=\n  ∀ (x : Bool) (L : Tape), ∃ n c, steps n ⟨cons false (cons x L), cons false s, .%s⟩ = some c ∧ step c = none\n"%(q,f,q))
    for form in 'VW':
        todo=[[0],[1]]
        while todo:
            p=todo.pop(0)
            r=rule(tm,form,p)
            if r is None:
                if len(p)<MAXP: todo += [p+[0],p+[1]]
                else:
                    found.append((form,p,None)); out.append('-- %s on `%s s`: no rule of this shape.\n'%(form,''.join(map(str,p))))
                continue
            found.append((form,p,r))
            ps=''.join(map(str,p))
            if r[0]=='ok':
                _,segs,subs,res,k=r
                rs=''.join(map(str,res))
                hyps=' '.join('(h%d : %s %s %s)'%(i+1, subs[i][0], svar(i,k), svar(i+1,k)) for i in range(k))
                doc='no nested visit' if k==0 else 'nested: '+', then '.join(s[0] for s in subs)
                out.append('/-- %s: `%s s` becomes `%s s\'`; %s. -/'%(form,ps,rs,doc))
                svs=' '.join(dict.fromkeys(svar(i,k) for i in range(k+1)))
                out.append('theorem %s_%s {%s : Tape} %s :\n    %s (%s) (%s) := by'%(form,ps, svs if k else 's', hyps, form, tape(p,'s'), tape(res, svar(k,k))))
                out.append('  intro x L')
                for i,(f,b,rest) in enumerate(subs):
                    out.append('  obtain ⟨n%d, e%d⟩ := h%d (%s) (%s)'%(i+1,i+1,i+1, b if isinstance(b,str) else B(b), tape(rest,'L')))
                for j,(a,n,b) in enumerate(segs):
                    out.append('  have a%d : steps %d %s = some %s := rfl'%(j,n,cfg(a,k),cfg(b,k)))
                expr='a0'; tot='%d'%segs[0][1]
                for i in range(k):
                    expr='steps_seq trans (steps_seq trans (%s) e%d) a%d'%(expr,i+1,i+1); tot+=' + n%d + %d'%(i+1,segs[i+1][1])
                out.append('  exact ⟨%s, %s⟩\n'%(tot,expr))
                for j in range(1,k+1):
                    hy=' '.join('(h%d : %s %s %s)'%(i+1, subs[i][0], svar(i,k+1), svar(i+1,k+1)) for i in range(j-1))
                    hy+=(' ' if hy else '')+'(h%d : %sH %s)'%(j, subs[j-1][0], svar(j-1,k+1))
                    svs2=' '.join(dict.fromkeys(svar(i,k+1) for i in range(j)))
                    out.append('/-- %s: a visit to `%s s` halts when its %s nested visit halts. -/'%(form,ps,['first','second','third'][j-1]))
                    out.append('theorem %s_%s_halts_%d {%s : Tape} %s :\n    %sH (%s) := by'%(form,ps,j,svs2,hy,form,tape(p,'s')))
                    out.append('  intro x L')
                    for i,(f,b,rest) in enumerate(subs[:j-1]):
                        out.append('  obtain ⟨n%d, e%d⟩ := h%d (%s) (%s)'%(i+1,i+1,i+1, b if isinstance(b,str) else B(b), tape(rest,'L')))
                    f,b,rest=subs[j-1]
                    out.append('  obtain ⟨m, c, e, hc⟩ := h%d (%s) (%s)'%(j, b if isinstance(b,str) else B(b), tape(rest,'L')))
                    for jj,(a,n,bb) in enumerate(segs[:j]):
                        out.append('  have a%d : steps %d %s = some %s := rfl'%(jj,n,cfg(a,k+1),cfg(bb,k+1)))
                    expr2='a0'; tot2='%d'%segs[0][1]
                    for i in range(j-1):
                        expr2='steps_seq trans (steps_seq trans (%s) e%d) a%d'%(expr2,i+1,i+1); tot2+=' + n%d + %d'%(i+1,segs[i+1][1])
                    out.append('  exact ⟨%s + m, c, steps_seq trans (%s) e, hc⟩\n'%(tot2,expr2))
            else:
                _,start,n,end,segs,subs=r
                k=len(subs)
                if k:
                    out.append('-- %s on `%s s`: halts after %d nested visit(s); not stated.\n'%(form,ps,k)); continue
                out.append('/-- %s: a visit to `%s s` halts. -/'%(form,ps))
                out.append('theorem %s_%s_halts {s : Tape} : %sH (%s) := by'%(form,ps,form,tape(p,'s')))
                out.append('  intro x L')
                out.append('  exact ⟨%d, %s, rfl, rfl⟩\n'%(n,cfg(end,0)))
    t,s0,k=top(tm, m)
    out += t
    out.append('end %s'%name)
    return '\n'.join(out)+'\n', found, s0, k
if __name__=='__main__':
    m=sys.argv[1]; name=sys.argv[2]
    src,found,s0,k=lean(name,m)
    open(sys.argv[3],'w').write(src)
    for f,p,r in found:
        print(f, ''.join(map(str,p)), 'none' if r is None else r[0], (''.join(map(str,r[3])),''.join(s[0] for s in r[2])) if r and r[0]=='ok' else '', file=sys.stderr)
    print('start', s0, k, file=sys.stderr)
