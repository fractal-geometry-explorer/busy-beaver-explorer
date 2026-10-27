"""Write EndgameTheorem.lean from endgame_trees.txt (lines 'R tokens...' written by ExploreNC)."""
import sys
lines = [l.split() for l in open(sys.argv[1]).read().strip().split('\n') if l.strip()]
out = sys.argv[2]
S = [2, 4, 8, 16, 24, 32, 48, 64, 176]
Rs = [int(l[0]) for l in lines]
assert sorted(Rs) == list(range(2, 4097, 2)), 'missing R'
data = ';'.join(' '.join(l) for l in lines if int(l[0]) not in S)
lean = r'''import BB6.Meets
open BB6 BB6.Sym

/-! # The endgame as a theorem

For every even R ≤ 4096 outside the closing set, a tree of coordinate splits of the phase-0 pass starts (built by the
untrusted program `ExploreNC.lean`, so it covers the start class by construction) is checked here by the proved
function `Tree.okNC`, evaluated with `native_decide` (this trusts Lean's compiler as well as its kernel).
`endgame_no_close` is the statement for the machine. -/

def startR (R : Nat) : List SMark × YForm × List YForm :=
  let a : YForm := ⟨1, [2, 0, 0]⟩
  let b : YForm := ⟨0, [0, 2, 0]⟩
  let E : YForm := ⟨0, [0, 0, 2]⟩
  let c := E.addc (-(R : Int) - 1)
  ([⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩], E, [a, b.sub a, c.sub b])

def decodeTree : Nat → List String → Option (Tree × List String)
  | 0, _ => none
  | _, [] => none
  | fuel + 1, tok :: rest =>
    if tok.startsWith "L" then some (.leaf (tok.drop 1).toString.toNat!, rest)
    else if tok.startsWith "N" then
      match decodeTree fuel rest with
      | some (t0, r1) =>
        match decodeTree fuel r1 with
        | some (t1, r2) => some (.node (tok.drop 1).toString.toNat! t0 t1, r2)
        | none => none
      | none => none
    else none

def closingSet : List Nat := CLOSING

def endgameData : String := "DATA"

def endgameTrees : List (Nat × Tree) :=
  (endgameData.splitOn ";").filterMap fun entry =>
    match (entry.splitOn " ").filter (· ≠ "") with
    | r :: toks => match decodeTree 400 toks with
      | some (t, []) => some (r.toNat!, t)
      | _ => none
    | [] => none

theorem endgame_trees_ok :
    (endgameTrees.all fun (p : Nat × Tree) => p.2.okNC 448 1000 3 (startR p.1).1 (startR p.1).2.1 (startR p.1).2.2) = true := by
  native_decide

theorem endgame_trees_cover :
    ((List.range 2048).all fun r => closingSet.contains (2 * (r + 1)) ||
      endgameTrees.any fun (p : Nat × Tree) => p.1 == 2 * (r + 1)) = true := by
  native_decide

/-- **The endgame, for the machine.**  For every even R with 2 ≤ R ≤ 4096 outside the closing set
{2, 4, 8, 16, 24, 32, 48, 64, 176}, and every phase-0 pass start — walls at a, b and c = E − R − 1, width E, with a
odd, b even, E even and every gap at least 448 — the machine runs a number of rounds (up to the round at which this
start's pass completes, its end-meeting chain breaks, or it leaves phase 0, per the tree) without halting, reaching a
round start (the one `roundsZ` computes: the mark model covers these rounds), and every end meeting on the way is at
distance at least 3: the run does not close. -/
theorem endgame_no_close (R : Nat) (hR : R % 2 = 0) (hR2 : 2 ≤ R) (hR4 : R ≤ 4096) (hS : closingSet.contains R = false)
    (a b E : Nat) (ha : a % 2 = 1) (hb : b % 2 = 0) (hE : E % 2 = 0)
    (h1 : 448 ≤ a) (h2 : a + 448 ≤ b) (h3 : b + 448 + R + 1 ≤ E) :
    ∃ n kk ms' W', steps kk (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E) = some (roundStart ms' W') ∧
      roundsZ 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E = .newRound ms' W' ∧
      ∀ d ∈ meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E, 3 ≤ d := by
  -- the tree for R
  have hcov := endgame_trees_cover
  rw [List.all_eq_true] at hcov
  have hr := hcov (R / 2 - 1) (by simp only [List.mem_range]; omega)
  have e : 2 * (R / 2 - 1 + 1) = R := by omega
  rw [e, hS, Bool.false_or, List.any_eq_true] at hr
  obtain ⟨⟨R', t⟩, hmem, hR'⟩ := hr
  simp only [beq_iff_eq] at hR'
  subst hR'
  have hok := endgame_trees_ok
  rw [List.all_eq_true] at hok
  have ht := hok _ hmem
  simp only at ht
  -- the point of the start class
  let y : List Int := [((a : Int) - 1) / 2, (b : Int) / 2, (E : Int) / 2]
  have hy : inCone (startR R').2.2 448 y := by
    intro f hf
    simp only [startR, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl <;>
      simp only [y, YForm.eval, YForm.sub, YForm.add, YForm.neg, YForm.addc, addL, smulL, List.map, dot] <;> omega
  have hs : agL y (startR R').1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R' - 1⟩] := by
    refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;>
      simp only [agN, y, startR, YForm.eval, YForm.addc, dot] <;> omega
  have hW : agN y (startR R').2.1 E := by simp only [agN, y, startR, YForm.eval, dot]; omega
  obtain ⟨n, kk, ms', W', hk, hr, hmeets⟩ := Tree.soundNC 448 1000 3 t _ _ _ ht y rfl hy _ _ hs hW
  exact ⟨n, kk, ms', W', hk, hr, hmeets⟩
'''
lean = lean.replace('DATA', data).replace('CLOSING', '[' + ', '.join(map(str, S)) + ']')
open(out, 'w').write(lean)
print('wrote', out, 'trees', len(lines) - len(S), 'chars', len(data))
