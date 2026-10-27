"""Write RouteTheorem.lean from a serialized route tree (built by ExploreRT).

usage: python3 gen_route.py route_tree.txt RouteTheorem.lean DEPTH GAMMA"""
import sys
data = open(sys.argv[1]).read().strip()
out = sys.argv[2]
D = int(sys.argv[3]); G = int(sys.argv[4])
toks = data.split()
for t in toks:
    assert t in ('C', 'K') or (t[0] in 'AS' and t[1:].isdigit()) or (t[0] == 'H' and t[1] in '01' and t[2] == ','), t
lean = r'''import BB6.RouteTree
open BB6 BB6.Sym

/-! # The route tree as a theorem

The tree below was built by the untrusted program `ExploreRT.lean` to depth DEPTH (splits by coordinates after
shears, so it covers the start class by construction) and is checked here by the proved function `RTree.ok`,
evaluated with `native_decide` (this trusts Lean's compiler as well as its kernel).  `route_tree_clean` is the
statement for the machine; `route_tree_cut_mass` is the measure of the starts it makes no claim for. -/

/-- The two-marker start class: m = 2 y₀, E = 1 + 2 y₁; marks M m, M E − 2, width E; cone gaps m and E − m. -/
def rtStart : List SMark × YForm × List YForm :=
  let m : YForm := ⟨0, [2, 0]⟩
  let E : YForm := ⟨1, [0, 2]⟩
  ([⟨.M, m⟩, ⟨.M, E.addc (-2)⟩], E, [m, E.sub m])

def decodeRT : Nat → List String → Option (RTree × List String)
  | 0, _ => none
  | _, [] => none
  | fuel + 1, tok :: rest =>
    if tok == "C" then some (.cut, rest)
    else if tok == "K" then some (.clean, rest)
    else if tok.startsWith "A" then
      match decodeRT fuel rest with
      | some (t, r) => some (.adv (tok.drop 1).toString.toNat! t, r)
      | none => none
    else if tok.startsWith "S" then
      match decodeRT fuel rest with
      | some (t0, r1) =>
        match decodeRT fuel r1 with
        | some (t1, r2) => some (.split (tok.drop 1).toString.toNat! t0 t1, r2)
        | none => none
      | none => none
    else if tok.startsWith "H" then
      match ((tok.drop 1).toString.splitOn ",") with
      | [i, s] =>
        match decodeRT fuel rest with
        | some (t, r) => some (.shear i.toNat! s.toInt! t, r)
        | none => none
      | _ => none
    else none

def routeData : String := "DATA"

def routeTree : RTree := match decodeRT 1000 ((routeData.splitOn " ").filter (· ≠ "")) with
  | some (t, []) => t
  | _ => .cut

theorem route_tree_ok : routeTree.ok GAMMA 1000 false rtStart.1 rtStart.2.1 rtStart.2.2 = true := by
  native_decide

/-- The cut leaves have measure `route_tree_cut_mass` / 2^DEPTH of the start class. -/
theorem route_tree_cut_mass : routeTree.cutMass DEPTH = CUTMASS ∧ routeTree.leaves = (NCUT, NCLEAN) := by
  native_decide

/-- **From a two-marker state with wide gaps, the machine reaches the next clean tape, unless the start is in a cut
class.**  For all naturals m, E with m even, E odd and both gaps at least GAMMA (m ≥ GAMMA, E − m ≥ GAMMA), the machine
started from the round start G 1, M m, M E − 2 (width E) runs n rounds of the mark model to a round start without
halting, and either n ≥ 1 and that round start is a clean tape (the gap at 1, at most one marker, the end marker),
or (m/2, (E − 1)/2) lies in one of the tree's cut classes (`routeTree.cutMem`), of total measure
`route_tree_cut_mass`. -/
theorem route_tree_clean (m E : Nat) (hm : m % 2 = 0) (hE : E % 2 = 1) (h1 : GAMMA ≤ m) (h2 : m + GAMMA ≤ E) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, m⟩, ⟨.M, E - 2⟩] E = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, m⟩, ⟨.M, E - 2⟩] E) = some (roundStart ms' W') ∧
      (routeTree.cutMem [(m : Int) / 2, ((E : Int) - 1) / 2] = true ∨ (0 < n ∧ cleanTape ms' W')) := by
  let y : List Int := [(m : Int) / 2, ((E : Int) - 1) / 2]
  have hy : inCone rtStart.2.2 GAMMA y := by
    intro t ht
    simp only [rtStart, List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl <;>
      simp only [y, YForm.eval, YForm.sub, YForm.add, YForm.neg, addL, smulL, List.map, dot] <;> omega
  have hs : agL y rtStart.1 [⟨.M, m⟩, ⟨.M, E - 2⟩] := by
    refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;>
      simp only [agN, y, YForm.eval, YForm.addc, dot] <;> omega
  have hW : agN y rtStart.2.1 E := by simp only [agN, y, rtStart, YForm.eval, dot]; omega
  have hwf : roundWF [⟨.M, m⟩, ⟨.M, E - 2⟩] E := by
    simp only [roundWF, rightOK, mval, mlen]
    refine ⟨by omega, ?_, by omega, ?_, by omega, ?_⟩
    all_goals (simp; omega)
  obtain ⟨n, k, ms', W', h1', h2', h3'⟩ :=
    RTree.sound GAMMA 1000 routeTree false _ _ _ route_tree_ok y rfl hy _ _ hs hW hwf
  refine ⟨n, k, ms', W', h1', h2', ?_⟩
  rcases h3' with h | ⟨h, hc⟩
  · exact Or.inl h
  · exact Or.inr ⟨by simpa using h, hc⟩
'''
# leaf counts and cut mass, recomputed here from the tokens (and checked again by the theorem)
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
