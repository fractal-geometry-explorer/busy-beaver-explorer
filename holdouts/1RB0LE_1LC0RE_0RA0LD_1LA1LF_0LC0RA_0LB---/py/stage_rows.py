"""The left visit rows (LVis) of 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LE---, written as Lean by a symbolic run; the rows of lean/Stage.lean.

usage: python3 .../py/stage_rows.py > rows.lean"""
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from wordchain import ptab
from latestage import M
T = ptab(M)
tr = {k: (v[0], v[1], v[2]) for k, v in T.items()}
S='ABCDEF'
def Bv(b): return 'true' if b else 'false'
def tape(cells, tail):
    s=tail
    for c in reversed(cells):
        s='cons %s (%s)'%(Bv(c), s)
    return s

def row(name, doc, tcells, q, nested_out, top=False):
    """tcells: cells of the unit left of its 0-cell, leftwards.  The nested stream starts at cell -(m+1)
    (cons false z_i) unless top (then blank from -(m+1) on).  nested_out: exit states of the nested visits in order."""
    m=len(tcells)
    cells={0:False}
    for i,c in enumerate(tcells): cells[-(i+1)]=bool(c)
    if not top: cells[-(m+1)]=False
    lo = -(m+1) if not top else -m      # leftmost explicit cell
    p=0; st=S.index(q)
    zi=0
    def zname(i): return 'z' if i==0 else 'z%d'%i
    def cfg():
        if p <= lo - 1 and top: raise Exception('top')
        left=[cells[j] for j in range(p-1, lo-1, -1)]
        if top: ltail='blank'
        else:
            if p == lo:  # head on the nested 0-cell: left is z_i
                left=[]; ltail=zname(zi)
            else:
                ltail=zname(zi)
        if not top and p != lo:
            pass
        right=[cells[j] for j in range(p, 1)]
        return '⟨%s, %s, .%s⟩'%(tape(left, ltail), tape(right, 'cons a R'), S[st])
    start=cfg()
    out=[]; hyps=[]; k=0; seg_start=start; nn=0
    def startleft():
        return tape([cells[j] for j in range(-1, lo-1, -1)], 'blank' if top else zname(0))
    y0=startleft()
    while True:
        x=tr[(S.index(S[st]) if False else st, cells[p] if p in cells else False)]
        if top and p not in cells: cells[p]=False
        cells[p]=bool(x[0]); p+=x[1]; st=x[2]; k+=1
        if top and p < lo:
            lo = p
        if p == 1:
            end=cfg()
            out.append(('seg', k, seg_start, end)); break
        if not top and p == -(m+1):
            # nested entry
            end=cfg()
            out.append(('seg', k, seg_start, end))
            qn=S[st]; rn=nested_out[nn]; nn+=1
            cell_right = cells[-m] if m>0 else None
            hyps.append((qn, zname(zi), rn, zname(zi+1)))
            zi+=1
            st=S.index(rn); p=-m
            cells[-(m+1)]=False
            seg_start=cfg(); k=0
            rest=tape([cells[j] for j in range(-m+1, 1)], 'cons a R')
            out.append(('nest', len(hyps), cells[-m], rest))
    # exit: left must be cons false y'
    assert cells[0] is False
    y1=tape([cells[j] for j in range(-1, lo-1, -1)], 'blank' if top else zname(zi))
    # Lean
    zs=' '.join(zname(i) for i in range(zi+1)) if not top else ''
    hs=' '.join('(h%d : LVis .%s %s .%s %s)'%(i+1,a,b,c,d) for i,(a,b,c,d) in enumerate(hyps))
    L=[]
    L.append('/-- %s -/'%doc)
    L.append('theorem %s%s %s :'%(name, (' {%s : Tape}'%zs) if zs else '', hs))
    L.append('    LVis .%s (%s) .%s (%s) := by'%(q, y0, S[st], y1))
    L.append('  intro a R')
    names=[]; si=0; ci=0
    for o in out:
        if o[0]=='seg':
            L.append('  have s%d : steps %d %s = some %s := rfl'%(si, o[1], o[2], o[3])); names.append('s%d'%si); si+=1
        else:
            i=o[1]
            # nested call: h_i applied to the cell right of the nested stream and the rest of the right tape
            L.append('  obtain ⟨t%d, c%d⟩ := h%d %s (%s)'%(i, i, i, Bv(o[2]), o[3])); names.append('c%d'%i)
    chain=names[-1]
    for n in reversed(names[:-1]):
        chain='steps_seq trans %s (%s)'%(n, chain)
    L.append('  exact ⟨_, %s⟩'%chain)
    return '\n'.join(L)

if __name__=='__main__':
    rows=[
      ('lv_d0', 'A digit 0 (`100`), entered in D: becomes 1, out in E.', [0,1], 'D', []),
      ('lv_d1', 'A digit 1 (`110`), entered in D: becomes 2, out in E.', [1,1], 'D', []),
      ('lv_d2', 'A digit 2 (`010`), entered in D: becomes 0 and carries (nested C→A, D→E, C→A), out in E.', [1,0], 'D', ['A','E','A']),
      ('lv_sep', 'A separator `1010`, entered in D: passes two increments (nested D→E, C→A, D→E, C→A), out in E.', [1,0,1], 'D', ['E','A','E','A']),
    ]
    for r in rows: print(row(*r)); print()
    print(row('lv_top', 'The top `1 0` and blank tape, entered in D: a new digit 0 below it, out in E.', [1], 'D', [], top=True))
