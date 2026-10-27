"""Write LoopPass.lean from loop_tree.txt (the serialized tree written by ExploreLoop)."""
import sys
data = open(sys.argv[1]).read().split()
out = sys.argv[2]
lean = r'''import BB6.Loop
open BB6 BB6.Sym

/-! # One stretch of the loop with the right end free

The phase-0 pass starts with R ≥ 4097 form one class, a = 1 + 2 y₀, b = 2 y₁, E = 2 y₂, R = 2 y₃, c = E − R − 1,
with cone gaps a, b − a, c − b and R − 3649 (all ≥ 448).  One tree of coordinate splits (built by the untrusted
program `ExploreLoop.lean`, so it covers the class by construction) is checked here by the proved function
`Tree.okLoop`, evaluated with `native_decide` (this trusts Lean's compiler as well as its kernel).  `loop_pass` is the
statement for the machine. -/

def loopStart : List SMark × YForm × List YForm :=
  let a : YForm := ⟨1, [2, 0, 0, 0]⟩
  let b : YForm := ⟨0, [0, 2, 0, 0]⟩
  let E : YForm := ⟨0, [0, 0, 2, 0]⟩
  let R : YForm := ⟨0, [0, 0, 0, 2]⟩
  let c := (E.sub R).addc (-1)
  ([⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩], E, [a, b.sub a, c.sub b, R.addc (448 - 4097)])

def loopR : YForm := ⟨0, [0, 0, 0, 2]⟩
def loopL : YForm := L1Form ⟨0, [0, 2, 0, 0]⟩ ((YForm.sub ⟨0, [0, 0, 2, 0]⟩ ⟨0, [0, 0, 0, 2]⟩).addc (-1)) ⟨0, [0, 0, 2, 0]⟩

def decodeLoop : Nat → List String → Option (Tree × List String)
  | 0, _ => none
  | _, [] => none
  | fuel + 1, tok :: rest =>
    if tok.startsWith "L" then some (.leaf (tok.drop 1).toString.toNat!, rest)
    else if tok.startsWith "N" then
      match decodeLoop fuel rest with
      | some (t0, r1) =>
        match decodeLoop fuel r1 with
        | some (t1, r2) => some (.node (tok.drop 1).toString.toNat! t0 t1, r2)
        | none => none
      | none => none
    else none

def loopData : String := "DATA"

def loopTree : Tree :=
  match decodeLoop 400 ((loopData.splitOn " ").filter (· ≠ "")) with
  | some (t, []) => t
  | _ => .leaf 0

theorem loop_tree_ok :
    loopTree.okLoop 448 1000 4 loopStart.1 loopStart.2.1 loopStart.2.2 loopR loopL = true := by
  native_decide

/-- **One stretch of the loop, for every width.**  For every phase-0 pass start with right end R ≥ 4097 — walls at
a, b and c = E − R − 1, width E, with a odd, b even, E even, R even and every gap at least 448 — the machine runs a
number of rounds without halting and without a close (every end meeting at distance ≥ 3), and the round start it
reaches is either not a phase-0 pass start, or a phase-0 pass start with every gap at least 448 and a smaller even
right end R′ > 176: a full pass, R′ = R/16 with left countdown L₁′ = L₁/64, or R′ = R/2. -/
theorem loop_pass (R a b E : Nat) (hR : R % 2 = 0) (hR4 : 4097 ≤ R) (ha : a % 2 = 1) (hb : b % 2 = 0)
    (hE : E % 2 = 0) (h1 : 448 ≤ a) (h2 : a + 448 ≤ b) (h3 : b + 448 + R + 1 ≤ E) :
    ∃ n kk ms' W', steps kk (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E) = some (roundStart ms' W') ∧
      roundsZ 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E = .newRound ms' W' ∧
      (∀ d ∈ meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E, 3 ≤ d) ∧
      LoopOut R (loopL1 b (E - R - 1) E) ms' W' := by
  let y : List Int := [((a : Int) - 1) / 2, (b : Int) / 2, (E : Int) / 2, (R : Int) / 2]
  have hy : inCone loopStart.2.2 448 y := by
    intro f hf
    simp only [loopStart, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl <;>
      simp only [y, YForm.eval, YForm.sub, YForm.add, YForm.neg, YForm.addc, addL, smulL, List.map, dot] <;> omega
  have hs : agL y loopStart.1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] := by
    refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;>
      simp only [agN, y, YForm.eval, YForm.sub, YForm.add, YForm.neg, YForm.addc, addL, smulL, List.map, dot] <;>
      omega
  have hW : agN y loopStart.2.1 E := by simp only [agN, y, loopStart, YForm.eval, dot]; omega
  have hRa : agN y loopR R := by simp only [agN, y, loopR, YForm.eval, dot]; omega
  have hL : loopL1 b (E - R - 1) E = loopL.eval y := by
    simp only [loopL, eval_L1Form, loopL1]
    simp only [y, YForm.eval, YForm.sub, YForm.add, YForm.neg, YForm.addc, addL, smulL, List.map, dot]
    omega
  exact Tree.soundLoop 448 1000 4 loopTree _ _ _ _ _ loop_tree_ok y rfl hy _ E R _ hs hW hRa hL
'''
lean = lean.replace('DATA', ' '.join(data))
open(out, 'w').write(lean)
print('wrote', out, 'tokens', len(data))
