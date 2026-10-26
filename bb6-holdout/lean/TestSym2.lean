import BB6.SymRound
open BB6 BB6.Sym

/-- The endgame start state of a leaf: G 1, W a, W b, W c = E − R − 1, width E, with
a = x0₀ + B₀₀ y₀, b = x0₁ + B₁₀ y₀ + B₁₁ y₁, E = x0₂ + B₂₀ y₀ + B₂₁ y₁ + B₂₂ y₂; the cone gaps a, b − a, c − b. -/
def leafStart (R : Int) (x0 : List Int) (B : List Int) : List SMark × YForm × List YForm :=
  let a : YForm := ⟨x0.getD 0 0, [B.getD 0 0, 0, 0]⟩
  let b : YForm := ⟨x0.getD 1 0, [B.getD 1 0, B.getD 2 0, 0]⟩
  let E : YForm := ⟨x0.getD 2 0, [B.getD 3 0, B.getD 4 0, B.getD 5 0]⟩
  let c := E.addc (-R - 1)
  ([⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩], E, [a, b.sub a, c.sub b])

def shapeOf (ss : List SMark) : String := "G" ++ String.join (ss.map (fun m => match m.t with
  | .G => "G" | .M => "M" | .W => "W" | .B => "B"))

/-- Run `n` rounds one at a time, reporting the shape after each. -/
def runLeaf (R : Int) (x0 B : List Int) (n : Nat) (Γ : Int) : List String := Id.run do
  let (ss, W, ts) := leafStart R x0 B
  let mut cur := ss
  let mut cw := W
  let mut out : List String := []
  for _ in [0:n] do
    match symRoundZ ts Γ 1000 [] (YForm.const 1) cur cw with
    | some (.newRound ss' W') => cur := ss'; cw := W'; out := out ++ [shapeOf ss']
    | some .uncovered => out := out ++ ["uncovered"]; return out
    | some .halt => out := out ++ ["halt"]; return out
    | some (.gap _ _ _ _) => out := out ++ ["gap?"]; return out
    | none => out := out ++ ["UNDECIDED"]; return out
  return out

#eval runLeaf 128 [1,30,8] [2,0,64,0,4,16] 10 448
#eval runLeaf 3264 [1,30,8] [2,0,64,0,4,16] 10 448
#eval runLeaf 6 [1,0,2] [2,0,4,0,4,16] 2 448
#eval runLeaf 14 [1,6,8] [2,0,16,0,0,16] 2 448
#eval runLeaf 76 [1,2,6] [2,0,4,0,8,16] 2 448
#eval runLeaf 6 [1,0,0] [2,0,4,0,0,4] 2 448
#eval runLeaf 30 [1,2,2] [2,0,4,0,0,4] 2 448
#eval runLeaf 254 [1,6,4] [2,0,8,0,0,8] 2 448
#eval runLeaf 2 [1,0,0] [2,0,4,0,0,4] 2 448
