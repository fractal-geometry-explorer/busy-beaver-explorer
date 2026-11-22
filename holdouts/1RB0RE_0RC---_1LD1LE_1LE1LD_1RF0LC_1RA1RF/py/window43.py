"""Writes the window of list step 28,450 into lean/Window.lean (the part between its two marker comments).

E reads the last 1 during a crossing with the 43-letter near part below.  The near side of the next six bounces does not
depend on the far part beyond its first three 4-cell letters `u v v`; this replays the six bounces on lists (the far
part kept symbolic: an even bounce turns it into `sx true X`, an odd one drops its head) and prints one Lean lemma per
bounce plus `window_W43`, which chains them.

  python3 window43.py > /tmp/w43.lean
"""
import re, sys
from turnshape import sx, par, rswL
W = [int(c) for c in '1010010000101000100010000000000000000000000']  # the near part when E read the last 1
L=lambda xs:'['+', '.join('true' if x else 'false' for x in xs)+']'
# The near side bounce by bounce; X is the far part's 4-cell word after its first u, as a Lean term.
N=list(W); s=[]; mode='EO'; absorbed=0
X='(false :: false :: Y)'
lines=[]
for b in range(6):
    Nabs=N+[0]*absorbed
    q=par(1,Nabs)
    tail=[] if mode=='EO' else [1]+s
    W2,e2,rest=rswL(0,[],list(reversed(sx(1,Nabs)))+tail)
    assert rest is not None
    if q:  # odd: far part f::f::dbl X ; X must start with true -> next absorbed 2, X := X.tail
        far=f"(false :: false :: dbl {X})"; nextX=f"({X}).tail"; nabs=2
    else:
        far=f"(false :: dbl (true :: sx true {X}))"; nextX=f"(sx true {X})"; nabs=1
    lines.append(dict(N=N,absorbed=absorbed,Nabs=Nabs,q=q,X=X,tail=tail,W2=W2,rest=rest,far=far,mode=mode))
    N,s,mode,absorbed=W2,rest,'T2',nabs
    # for odd, the next X is the tail, and the far part dbl X must be dbl (true :: X.tail)
    X=nextX if not q else nextX
# Lean
src=[]
src.append('/-! ## The window after list step 28,450 (four of the ten turns)\n\nThe zone is 43 letters; the far part only has to start with `u v v` (`dbl (true :: false :: false :: Y)`).  Written by\n`py/window43.py`. -/\n')
src.append(f"def W43 : List Bool := {L(W)}\n")
for i,l in enumerate(lines):
    st_src = (f".EO W43 (some (dbl (true :: false :: false :: Y))) p" if i==0 else f".T2 {L(lines[i]['N'])} {lines[i-1]['far']} p {L(lines[i-1]['rest'])} false")
    nxt = f".T2 {L(l['W2'])} {l['far']} q {L(l['rest'])} false"
    t = 'true :: '+L(l['tail'][1:]) if l['mode']=='T2' else '[]'
    lem='core_odd' if l['q'] else 'core_even'
    qexpr = 'p' if l['q'] else f"bne p (par false (dbl (true :: {l['X']})))"
    Xl = l['X']
    src.append(f"""theorem w43_step{i+1} (Y : List Bool) (p : Bool) :
    ∃ q, astep ({st_src}) = some ({nxt}) := by
  refine ⟨{qexpr}, ?_⟩
  show coreO {L(l['Nabs'])} (dbl (true :: {Xl})) p {('(true :: ' + L(l['tail'][1:])+')') if l['mode']=='T2' else '[]'} false = _
  rw [{lem} _ _ _ _ _ rfl]
  rfl
""")
OUT = '\n'.join(src)
# witness decomposition of final s
b=''.join(map(str,s))
for m in re.finditer(r'1+',b):
    if m.start()>0 and b[m.start()-1]=='0' and len(m.group())%2:
        i0=m.start()-1; k=(len(m.group())-1)//2; v=s[m.end():]
        break
b=''.join(map(str,s))
for m in re.finditer(r'1+',b):
    if m.start()>0 and b[m.start()-1]=='0' and len(m.group())%2:
        i0=m.start()-1; k=(len(m.group())-1)//2; v=s[m.end():]; u=s[:i0]; break
n=len(lines)
fin=f"""
/-- **The window after list step 28,450 is safe** for every far part starting `u v v`: six list steps, the last of
which leaves a witness. -/
theorem window_W43 (Y : List Bool) (p : Bool) : SafeWithin {n} (.EO W43 (some (dbl (true :: false :: false :: Y))) p) := by
"""
prev='p'
for i in range(n):
    fin+=f"  obtain ⟨q{i+1}, h{i+1}⟩ := w43_step{i+1} Y {prev}\n"; prev=f"q{i+1}"
expr=f"safeWithin_of_safe 0 _ (Or.inr ⟨⟨2, _, rfl⟩, {L(u)}, {k}, {L(v)}, by simp, rfl⟩)"
for i in reversed(range(n)):
    expr=f"safeWithin_of_step _ _ _ h{i+1} ({expr})"
fin+="  exact "+expr+"\n"
OUT += fin
sys.stdout.write(OUT)
