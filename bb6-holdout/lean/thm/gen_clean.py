"""Write CleanTheorem.lean from a serialized clean-tape tree (built by ExploreCT).

usage: python3 gen_clean.py clean_tree.txt CleanTheorem.lean DEPTH GAMMA"""
import sys
data = open(sys.argv[1]).read().strip()
out = sys.argv[2]
D = int(sys.argv[3]); G = int(sys.argv[4])
toks = data.split()
for t in toks:
    assert t in ('C', 'K') or (t[0] in 'AS' and t[1:].isdigit()) or (t[0] == 'H' and t[1] in '01' and t[2] == ','), t
lean = r'''import BB6.CleanTree
open BB6 BB6.Sym

/-! # The clean-tape tree as a theorem

The tree below was built by the untrusted program `ExploreCT.lean` to depth DEPTH (splits on the binary digits of
W/2, so it covers the start class by construction) and is checked here by the proved function `RTree.okW`, evaluated
with `native_decide` (this trusts Lean's compiler as well as its kernel).  `clean_tree_step` is the statement for the
machine; `clean_tree_cut_mass` is the measure of the starts it makes no claim for. -/

/-- The clean-tape start class: W = 2 y₀ (y₁ unused); the marker M W − 2, width W; cone W ≥ Γ. -/
def ctStart : List SMark × YForm × List YForm :=
  let W : YForm := ⟨0, [2, 0]⟩
  ([⟨.M, W.addc (-2)⟩], W, [W])

def cleanGamma : Nat := GAMMA

def decodeCT : Nat → List String → Option (RTree × List String)
  | 0, _ => none
  | _, [] => none
  | fuel + 1, tok :: rest =>
    if tok == "C" then some (.cut, rest)
    else if tok == "K" then some (.clean, rest)
    else if tok.startsWith "A" then
      match decodeCT fuel rest with
      | some (t, r) => some (.adv (tok.drop 1).toString.toNat! t, r)
      | none => none
    else if tok.startsWith "S" then
      match decodeCT fuel rest with
      | some (t0, r1) =>
        match decodeCT fuel r1 with
        | some (t1, r2) => some (.split (tok.drop 1).toString.toNat! t0 t1, r2)
        | none => none
      | none => none
    else if tok.startsWith "H" then
      match ((tok.drop 1).toString.splitOn ",") with
      | [i, s] =>
        match decodeCT fuel rest with
        | some (t, r) => some (.shear i.toNat! s.toInt! t, r)
        | none => none
      | _ => none
    else none

def cleanData : String := "DATA"

def cleanTree : RTree := match decodeCT 1000 ((cleanData.splitOn " ").filter (· ≠ "")) with
  | some (t, []) => t
  | _ => .cut

theorem clean_tree_ok :
    cleanTree.okW cleanGamma 1000 false ctStart.1 ctStart.2.1 ctStart.2.1 ctStart.2.2 = true := by
  native_decide

/-- The cut leaves have measure `clean_tree_cut_mass` / 2^DEPTH of the start class. -/
theorem clean_tree_cut_mass : cleanTree.cutMass DEPTH = CUTMASS ∧ cleanTree.leaves = (NCUT, NCLEAN) := by
  native_decide

/-- **From a clean tape of width at least GAMMA, the machine reaches a wider clean tape, unless W/2 is in a cut
class.**  For every even W ≥ GAMMA, the machine started from the round start G 1, M W − 2 (width W) runs n rounds of the
mark model to a round start without halting, and either n ≥ 1 and that round start is a one-marker clean tape of
width W′ > W, or W/2 lies in one of the tree's cut classes (`cleanTree.cutMem`: residue classes of W/2 modulo powers
of two up to 2^DEPTH), of total measure `clean_tree_cut_mass`. -/
theorem clean_tree_step (W : Nat) (hW : W % 2 = 0) (h : cleanGamma ≤ W) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
      (cleanTree.cutMem [(W : Int) / 2, 0] = true ∨ (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W')) := by
  simp only [cleanGamma] at h
  let y : List Int := [(W : Int) / 2, 0]
  have hy : inCone ctStart.2.2 cleanGamma y := by
    intro t ht
    simp only [ctStart, List.mem_cons, List.mem_nil_iff, or_false] at ht
    subst ht
    simp only [cleanGamma, y, YForm.eval, dot]
    omega
  have hs : agL y ctStart.1 [⟨.M, W - 2⟩] := by
    refine ⟨⟨rfl, ?_⟩, trivial⟩
    simp only [agN, y, YForm.eval, YForm.addc, dot]
    omega
  have hW' : agN y ctStart.2.1 W := by simp only [agN, y, ctStart, YForm.eval, dot]; omega
  have hwf : roundWF [⟨.M, W - 2⟩] W := roundWF_one.mpr ⟨by omega, hW⟩
  obtain ⟨n, k, ms', W', h1', h2', h3'⟩ :=
    RTree.soundW cleanGamma 1000 cleanTree false _ _ _ _ clean_tree_ok y rfl hy _ _ _ hs hW' hW' hwf
  refine ⟨n, k, ms', W', h1', h2', ?_⟩
  rcases h3' with h | ⟨h, hc⟩
  · exact Or.inl h
  · exact Or.inr ⟨by simpa using h, hc⟩
'''
def parse(i, depth):
    t = toks[i]
    if t == 'C': return i + 1, 2 ** (D - depth), 1, 0
    if t == 'K': return i + 1, 0, 0, 1
    if t[0] in 'AH': return parse(i + 1, depth)
    j, m0, c0, k0 = parse(i + 1, depth + 1)
    j, m1, c1, k1 = parse(j, depth + 1)
    return j, m0 + m1, c0 + c1, k0 + k1
sys.setrecursionlimit(100000)
j, mass, ncut, nclean = parse(0, 0)
assert j == len(toks)
lean = lean.replace('DATA', data).replace('DEPTH', str(D)).replace('GAMMA', str(G))
lean = lean.replace('CUTMASS', str(mass)).replace('NCUT', str(ncut)).replace('NCLEAN', str(nclean))
open(out, 'w').write(lean)
print('wrote', out, len(toks), 'tokens; cut mass %d / 2^%d = %.4e; leaves cut %d clean %d' % (mass, D, mass / 2 ** D, ncut, nclean))
