"""Write PassMaps.lean: the extra-wall pass maps P and Q as theorems about the proved symbolic model.

Reads the cosets (`../cosets.json`, untrusted Python output) and the affine maps (`../passmaps.py`), computes the image
forms in the coset coordinates (exact rationals; asserts they are integral), and emits Lean that runs the symbolic
zipper model 8 rounds on each coset and checks shapes and final positions by `native_decide`.
usage: python3 gen_passmaps.py [GammaP GammaQ]   (writes PassMaps.lean next to this script)"""
import json, os, sys
from fractions import Fraction as F
from math import lcm

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
from passmaps import MAPS

SHAPES = {'P': 'GBWW GWWWW GBWW GMBW GMWWW GMBW GMWWW GWWWW'.split(),
          'Q': 'GBWW GMMWW GMWWW GMBW GMWWW GMBW GMWWW GWWWW'.split()}
GAMMA = {'P': int(sys.argv[1]) if len(sys.argv) > 2 else 36, 'Q': int(sys.argv[2]) if len(sys.argv) > 2 else 192}
VARS = ['w1', 'w2', 'w3', 'w4', 'E']
C = json.load(open(os.path.join(HERE, '..', 'cosets.json')))


def form(k, c):
    return '⟨%d, [%s]⟩' % (k, ', '.join(str(v) for v in c))


def lin(coefs, const, names):
    """Lean Nat expression sum coefs*names + const (coefs, const nonnegative integers)."""
    parts = []
    for a, n in zip(coefs, names):
        if a == 0: continue
        parts.append(n if a == 1 else f'{a} * {n}')
    if const: parts.append(str(const))
    return ' + '.join(parts) if parts else '0'


def section(name):
    x0 = [int(v) for v in C[name]['x0']]
    B = [[int(v) for v in r] for r in C[name]['basis']]
    M = MAPS[name]
    G = GAMMA[name]
    start = [(x0[j], [B[i][j] for i in range(5)]) for j in range(5)]
    img = []
    for j in range(5):
        k = sum(M[j][l] * x0[l] for l in range(5)) + M[j][5]
        c = [sum(M[j][l] * B[i][l] for l in range(5)) for i in range(5)]
        assert k.denominator == 1 and all(v.denominator == 1 for v in c), (name, j)
        img.append((int(k), [int(v) for v in c]))
    ks = ['k0', 'k1', 'k2', 'k3', 'k4']
    # coset membership hypotheses
    hyps = []
    for j in range(5):
        k, c = start[j]
        rhs = ' + '.join([str(k)] + [f'({c[i]}) * {ks[i]}' for i in range(5) if c[i] != 0])
        hyps.append(f'(h{VARS[j]} : ({VARS[j]} : Int) = {rhs})')
    # map equations: D * new = sum (D*coef) old + D*const
    neq = []
    newv = ['v1', 'v2', 'v3', 'v4', "E'"]
    for j in range(5):
        D = lcm(*[x.denominator for x in M[j]])
        co = [int(x * D) for x in M[j][:5]]
        cst = int(M[j][5] * D)
        assert all(v >= 0 for v in co) and cst >= 0
        lhs = newv[j] if D == 1 else f'{D} * {newv[j]}'
        neq.append(f'{lhs} = {lin(co, cst, VARS)}')
    s = f'''
/-! ## The pass map {name}

Coset of starts (coordinates k0 … k4; positions x = x0 + Σ kᵢ·basisᵢ from `cosets.json`).  Shapes of the 8 rounds:
{' '.join(SHAPES[name])}. -/

def {name}w1 : YForm := {form(*start[0])}
def {name}w2 : YForm := {form(*start[1])}
def {name}w3 : YForm := {form(*start[2])}
def {name}w4 : YForm := {form(*start[3])}
def {name}E : YForm := {form(*start[4])}
def {name}ss : List SMark := [⟨.W, {name}w1⟩, ⟨.W, {name}w2⟩, ⟨.W, {name}w3⟩, ⟨.W, {name}w4⟩]
def {name}ts : List YForm := [{name}w1, {name}w2.sub {name}w1, {name}w3.sub {name}w2, {name}w4.sub {name}w3, {name}E.sub {name}w4]
/-- The affine image of the start, as forms in the same coordinates. -/
def {name}tt : List SMark := [⟨.W, {form(*img[0])}⟩, ⟨.W, {form(*img[1])}⟩, ⟨.W, {form(*img[2])}⟩, ⟨.W, {form(*img[3])}⟩]
def {name}tW : YForm := {form(*img[4])}

/-- Evaluated: the start is well formed on the cone (gaps ≥ {G}), every one of the 8 rounds is decided and ends at a
round start, and the positions after round 8 are the affine image. -/
theorem {name}_check : passCheck {name}ts {G} 1000 8 {name}ss {name}E {name}tt {name}tW = true := by native_decide

/-- Evaluated: the shapes of the 8 rounds. -/
theorem {name}_shapes : symShapes {name}ts {G} 1000 8 {name}ss {name}E =
    some {json.dumps(SHAPES[name]).replace(', ', ', ')} := by native_decide

/-- **The pass map {name}, for the machine.**  Every round start `G 1, W w1, W w2, W w3, W w4`, width `E`, on the
coset of {name} with all cone gaps at least {G} runs in some number `kk` of machine steps, without halting, to the round
start `G 1, W v1, W v2, W v3, W v4`, width `E'`, where (v1, v2, v3, v4, E') is the affine image {name}(w1, …, E); this
is also the 8-round result of the proved zipper model `roundsZ`. -/
theorem {name}_pass (k0 k1 k2 k3 k4 : Int) (w1 w2 w3 w4 E : Nat)
    {' '.join(hyps[:3])}
    {' '.join(hyps[3:])}
    (g1 : {G} ≤ w1) (g2 : w1 + {G} ≤ w2) (g3 : w2 + {G} ≤ w3) (g4 : w3 + {G} ≤ w4) (g5 : w4 + {G} ≤ E) :
    ∃ kk v1 v2 v3 v4 E', steps kk (roundStart [⟨.W, w1⟩, ⟨.W, w2⟩, ⟨.W, w3⟩, ⟨.W, w4⟩] E) =
        some (roundStart [⟨.W, v1⟩, ⟨.W, v2⟩, ⟨.W, v3⟩, ⟨.W, v4⟩] E') ∧
      roundsZ 1000 8 [⟨.W, w1⟩, ⟨.W, w2⟩, ⟨.W, w3⟩, ⟨.W, w4⟩] E =
        .newRound [⟨.W, v1⟩, ⟨.W, v2⟩, ⟨.W, v3⟩, ⟨.W, v4⟩] E' ∧
      {neq[0]} ∧
      {neq[1]} ∧
      {neq[2]} ∧
      {neq[3]} ∧
      {neq[4]} := by
  let y : List Int := [k0, k1, k2, k3, k4]
  have hy : inCone {name}ts {G} y := by
    intro t ht
    simp only [{name}ts, List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl <;>
      simp only [y, {name}w1, {name}w2, {name}w3, {name}w4, {name}E, YForm.eval, YForm.sub, YForm.add, YForm.neg, addL, smulL,
        List.map, dot] <;> omega
  have hs : agL y {name}ss [⟨.W, w1⟩, ⟨.W, w2⟩, ⟨.W, w3⟩, ⟨.W, w4⟩] := by
    refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;>
      simp only [agN, y, {name}w1, {name}w2, {name}w3, {name}w4, YForm.eval, dot] <;> omega
  have hW : agN y {name}E E := by simp only [agN, y, {name}E, YForm.eval, dot]; omega
  obtain ⟨kk, ms', Wn', hk, hr, ht, htW⟩ := pass_sound _ _ _ _ _ _ _ _ {name}_check y hy _ _ hs hW
  obtain ⟨v1, v2, v3, v4, rfl, e1, e2, e3, e4⟩ := agL_four ht
  refine ⟨kk, v1, v2, v3, v4, Wn', hk, hr, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [agN, y, {name}tW, YForm.eval, dot] at e1 e2 e3 e4 htW <;> omega
'''
    return s


HEADER = '''import BB6.SymSplit
open BB6 BB6.Sym

/-! # The pass maps P and Q of the one-extra-wall loop, as theorems

Generated by `gen_passmaps.py` from `../cosets.json` and `../passmaps.py`.  For each map, the start state on its coset
is built with positions as forms in the coset coordinates; the proved symbolic model `symRoundsZ` is run for 8
rounds; `passCheck` (evaluated by `native_decide`, which trusts Lean's compiler as well as its kernel) confirms that
the start is well formed on the cone, every round is decided, and the final positions equal the affine image as
forms.  `pass_sound` (proved, from `symRoundsZ_sound`, `symRightOK_sound` and `rounds_run`) turns this into a
statement about the machine, and `P_pass` / `Q_pass` state it in plain terms.  No split was needed: both cosets are
decided as they are. -/

namespace BB6.Sym

/-- Coefficientwise equality of forms. -/
def formEqB (f g : YForm) : Bool := f.k == g.k && coeffEq f.c g.c

theorem eval_formEqB {f g : YForm} (h : formEqB f g = true) (y : List Int) : f.eval y = g.eval y := by
  simp only [formEqB, Bool.and_eq_true, beq_iff_eq] at h
  simp only [YForm.eval, h.1, dot_coeffEq _ _ y h.2]

def marksEqB : List SMark → List SMark → Bool
  | [], [] => true
  | s :: ss, t :: tt => decide (s.t = t.t) && formEqB s.p t.p && marksEqB ss tt
  | _, _ => false

theorem agL_marksEqB {y : List Int} : ∀ {ss tt : List SMark} {ms : List Mark}, marksEqB ss tt = true → agL y ss ms →
    agL y tt ms
  | [], [], [], _, _ => trivial
  | s :: ss, t :: tt, m :: ms, h, hs => by
    simp only [marksEqB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨⟨ht, hp⟩, hr⟩ := hs
    refine ⟨⟨h1 ▸ ht, ?_⟩, agL_marksEqB h3 hr⟩
    unfold agN at hp ⊢; rw [hp, eval_formEqB h2]
  | [], _ :: _, _, h, _ => by simp [marksEqB] at h
  | _ :: _, [], _, h, _ => by simp [marksEqB] at h
  | [], [], _ :: _, _, hs => absurd hs id
  | _ :: _, _ :: _, [], _, hs => absurd hs id

section
variable (ts : List YForm) (Γ : Int)

/-- The pass check: well-formed start, `n` decided rounds ending at a round start whose marks and width are, as forms,
`tt` and `tW`. -/
def passCheck (fuel n : Nat) (ss : List SMark) (sW : YForm) (tt : List SMark) (tW : YForm) : Bool :=
  symRightOK ts Γ (YForm.const 4) false sW ss &&
  (match symRoundsZ ts Γ fuel n ss sW with
   | some (.newRound ss' sW') => marksEqB ss' tt && formEqB sW' tW
   | _ => false)

def shapeOf (ss : List SMark) : String := "G" ++ String.join (ss.map (fun m => match m.t with
  | .G => "G" | .M => "M" | .W => "W" | .B => "B"))

/-- The shapes of the round starts of `n` symbolic rounds (`none` unless every round is decided and ends at a round
start). -/
def symShapes (fuel : Nat) : Nat → List SMark → YForm → Option (List String)
  | 0, _, _ => some []
  | n + 1, ss, sW =>
    match symRoundZ ts Γ fuel [] (YForm.const 1) ss sW with
    | some (.newRound ss' sW') => (symShapes fuel n ss' sW').map (shapeOf ss' :: ·)
    | _ => none

theorem pass_sound (fuel n : Nat) (ss : List SMark) (sW : YForm) (tt : List SMark) (tW : YForm)
    (hc : passCheck ts Γ fuel n ss sW tt tW = true)
    (y : List Int) (hy : inCone ts Γ y) (ms : List Mark) (Wn : Nat) (hs : agL y ss ms) (hW : agN y sW Wn) :
    ∃ k ms' Wn', steps k (roundStart ms Wn) = some (roundStart ms' Wn') ∧ roundsZ fuel n ms Wn = .newRound ms' Wn' ∧
      agL y tt ms' ∧ agN y tW Wn' := by
  simp only [passCheck, Bool.and_eq_true] at hc
  obtain ⟨hwf, hrun⟩ := hc
  cases hr : symRoundsZ ts Γ fuel n ss sW with
  | none => rw [hr] at hrun; cases hrun
  | some r =>
    rw [hr] at hrun
    cases r with
    | newRound ss' sW' =>
      simp only [Bool.and_eq_true] at hrun
      have hag := symRoundsZ_sound ts Γ hy fuel n ss ms sW Wn _ hs hW hr
      have hrwf : roundWF ms Wn := symRightOK_sound ts Γ hy ss _ 4 false sW Wn ms (agN_const y 4) hW hs hwf
      generalize hcr : roundsZ fuel n ms Wn = cr at hag
      cases cr with
      | newRound ms' Wn' =>
        obtain ⟨k, hk, -⟩ := rounds_run fuel n ms Wn hrwf (by rw [hcr]; intro h; cases h)
        rw [hcr] at hk
        refine ⟨k, ms', Wn', hk, rfl, agL_marksEqB hrun.1 hag.1, ?_⟩
        have := hag.2; unfold agN at this ⊢; rw [this, eval_formEqB hrun.2]
      | _ => exact absurd hag id
    | _ => simp at hrun

end

theorem agL_four {y : List Int} {f1 f2 f3 f4 : YForm} {ms : List Mark}
    (h : agL y [⟨.W, f1⟩, ⟨.W, f2⟩, ⟨.W, f3⟩, ⟨.W, f4⟩] ms) :
    ∃ v1 v2 v3 v4, ms = [⟨.W, v1⟩, ⟨.W, v2⟩, ⟨.W, v3⟩, ⟨.W, v4⟩] ∧ agN y f1 v1 ∧ agN y f2 v2 ∧ agN y f3 v3 ∧
      agN y f4 v4 := by
  match ms, h with
  | [⟨t1, p1⟩, ⟨t2, p2⟩, ⟨t3, p3⟩, ⟨t4, p4⟩], ⟨⟨e1, a1⟩, ⟨e2, a2⟩, ⟨e3, a3⟩, ⟨e4, a4⟩, _⟩ =>
    simp only at e1 e2 e3 e4
    subst e1 e2 e3 e4
    exact ⟨p1, p2, p3, p4, rfl, a1, a2, a3, a4⟩

end BB6.Sym

open BB6.Sym
'''

FOOTER = '''
#print axioms P_pass
#print axioms Q_pass
'''

if __name__ == '__main__':
    out = os.path.join(HERE, 'PassMaps.lean')
    text = HEADER + section('P') + section('Q') + FOOTER
    open(out, 'w').write(text)
    # the same file with every evaluation done by the kernel (no compiler trust; about 5 minutes)
    outk = os.path.join(HERE, 'PassMapsKernel.lean')
    open(outk, 'w').write(text.replace(':= by native_decide', ':= by decide +kernel'))
    print('wrote', out, outk, GAMMA)
