"""Write ExitTheorem.lean from exit_tree.txt (the serialized tree built by ExploreExit).
usage: gen_exit.py exit_tree.txt ExitTheorem.lean [budget]"""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from treegen import parse, cut, pieces_lean, leaves, OK
toks = open(sys.argv[1]).read().split()
out = sys.argv[2]
budget = int(sys.argv[3]) if len(sys.argv) > 3 else 40
tree = parse(toks)
kind = OK('390 1000 4')
skel, proof, pieces = cut(tree, kind, 'exitStart', 'exitP', budget)
lean = r'''import BB6.Meets
open BB6 BB6.Sym

/-! # The exit certificate as a theorem

The tree below was built by the untrusted program `ExploreExit.lean` (coordinate splits and skews, so it covers the
start class by construction; `adv` nodes run the rounds before a split once for the whole subtree) and is checked
here by the proved function `Tree.ok`, evaluated by the kernel
(`decide +kernel`; no compiler is trusted).  The check is cut into subtrees `exitP0`, `exitP1`, … with a theorem each
(one kernel evaluation of the whole check would hold too many terms in memory), assembled into `exit_tree_ok` by
`Tree.ok_node` and `Tree.ok_skew`.  `exit_no_halt` is the statement for the machine. -/

def exitStart : SState :=
  let a : YForm := ⟨1, [2, 0, 0, 0]⟩
  let b : YForm := ⟨0, [0, 2, 0, 0]⟩
  let c : YForm := ⟨1, [0, 0, 2, 0]⟩
  let E : YForm := ⟨0, [0, 0, 0, 2]⟩
  ([⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩], E, [a, b.sub a, c.sub b, E.sub c])

PIECES
def exitTree : Tree := SKEL

theorem exit_tree_ok : exitTree.ok 390 1000 4 false exitStart.1 exitStart.2.1 exitStart.2.2 = true :=
  PROOF

/-- **From any loop state with large gaps, the machine runs on without halting.**  For all naturals a, b, c, E with
a odd, b even, c odd, E even and every gap at least 390 (a ≥ 390, b − a ≥ 390, c − b ≥ 390, E − c ≥ 390), the machine
started from the round start with walls at a, b, c and width E reaches, after some number n of rounds (the round at
which this state's run breaks off, cleans the tape or completes a pass, per the tree), another round start; it does
not halt on the way. -/
theorem exit_no_halt (a b c E : Nat) (ha : a % 2 = 1) (hb : b % 2 = 0) (hc : c % 2 = 1) (hE : E % 2 = 0)
    (h1 : 390 ≤ a) (h2 : a + 390 ≤ b) (h3 : b + 390 ≤ c) (h4 : c + 390 ≤ E) :
    ∃ n kk ms' W', steps kk (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E) = some (roundStart ms' W') ∧
      roundsZ 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E = .newRound ms' W' := by
  let y : List Int := [((a : Int) - 1) / 2, (b : Int) / 2, ((c : Int) - 1) / 2, (E : Int) / 2]
  have hy : inCone exitStart.2.2 390 y := by
    intro t ht
    simp only [exitStart, List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl <;>
      simp only [y, YForm.eval, YForm.sub, YForm.add, YForm.neg, addL, smulL, List.map, dot] <;> omega
  have hs : agL y exitStart.1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] := by
    refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;>
      simp only [agN, y, exitStart, YForm.eval, dot] <;> omega
  have hW : agN y exitStart.2.1 E := by simp only [agN, y, YForm.eval, dot]; omega
  exact Tree.sound 390 1000 4 exitTree false _ _ _ exit_tree_ok y rfl hy _ _ hs hW (fun h => by cases h)
'''
lean = lean.replace('PIECES', pieces_lean(kind, pieces)).replace('SKEL', skel).replace('PROOF', proof)
open(out, 'w').write(lean)
print('wrote', out, len(toks), 'tokens,', leaves(tree), 'leaves,', len(pieces), 'subtree theorems')
