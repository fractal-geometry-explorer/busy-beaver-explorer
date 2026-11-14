#!/usr/bin/env python3
"""Write the segment files.  usage: mkseg.py OUTDIR K   (K = number of rounds before the halting round)"""
# NOTE: reads the boundary words from the scratch directory of the session that produced them (P below); kept as a record.
import sys,os
P='/mnt/project-files/f02/seg'; out=sys.argv[1]; K=int(sys.argv[2])
bs=[0,57000,80600,98700,114000,127400,139600,145300,150800,156100,K]
ONLY=sys.argv[3:]  # optional: write only Words for these boundaries (testing)
for k in bs[1:]:
    if not os.path.exists(f'{P}/s_{k}.txt'): continue
    l,h=open(f'{P}/s_{k}.txt').read().split()
    open(f'{out}/VisitW{k}.lean','w').write(f"""import VisitSeg

/-! The word after {k} rounds as a number (`dec l{k} n{k}`: the `l{k}` low bits of `n{k}`, lowest first).  Written by
the checker itself (`Gen.lean`); nothing is claimed here, the segment files check it. -/

namespace VisitLaw.Run

def l{k} : Nat := {l}
def n{k} : Nat := 0x{h}

end VisitLaw.Run
""")
for i in range(1,len(bs)):
    a,b=bs[i-1],bs[i]
    imp=(f'import VisitW{b}' if a==0 else f'import VisitW{a}\nimport VisitW{b}')
    stmt=f'segFrom {b} [true] l{b} n{b}' if a==0 else f'seg {b-a} l{a} n{a} l{b} n{b}'
    open(f'{out}/VisitSeg{i}.lean','w').write(f'''{imp}

/-! Rounds {a+1} to {b}: the checker takes the word after {a} rounds to the word after {b} rounds (`native_decide`). -/

namespace VisitLaw.Run

theorem seg{i} : {stmt} = true := by native_decide

end VisitLaw.Run
''')
n=len(bs)-1
L=['\n'.join(f'import VisitSeg{i}' for i in range(1,n+1)),'',
f'/-! `check {K} [true] = true`: the {n} segments chained (`iter_add`), then the halting round {K+1} (`native_decide`). -/','',
'namespace VisitLaw.Run','',
f'theorem last : hscan fuelR 0 0 (true :: false :: dec l{K} n{K}) = true := by native_decide','',
f'theorem reach{bs[1]} : iter {bs[1]} [true] = some (dec l{bs[1]} n{bs[1]}) := segFrom_sound seg1\n']
for i in range(2,n+1):
    a,b=bs[i-1],bs[i]
    L.append(f'theorem reach{b} : iter {b} [true] = some (dec l{b} n{b}) := by\n  have h := iter_add (b := {b-a}) reach{a}\n  rw [show {b-a} + {a} = {b} from rfl] at h\n  exact h.trans (seg_sound seg{i})\n')
L.append(f'/-- After {K} rounds from the word `1` the next round halts. -/\ntheorem check_run : check {K} [true] = true := check_of reach{K} last\n')
L.append('end VisitLaw.Run\n')
open(f'{out}/VisitRun.lean','w').write('\n'.join(L))
