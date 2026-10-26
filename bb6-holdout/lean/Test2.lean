import BB6.Round
open BB6

instance : BEq MarkT := ⟨fun a b => decide (a = b)⟩
instance : BEq Mark := ⟨fun a b => a.t == b.t && a.p == b.p⟩

def showPR : PR' → String
  | .newRound ms W => s!"next W={W} marks={ms.length}"
  | .gap _ g _ W => s!"gap {g} W={W}"
  | .halt => "halt"
  | .uncovered => "uncovered"

/-- Run both models side by side from a round start; report the first disagreement. -/
def cmp : Nat → Nat → List Mark → Nat → String
  | 0, i, _, W => s!"agree for {i} rounds; final W {W}"
  | n + 1, i, ms, W =>
    let z := roundZ 1000 [] 1 ms W
    let o := Model.round ⟨⟨.G, 1⟩ :: ms, W⟩
    match z, o with
    | .newRound ms' W', .next s =>
      if s.marks == (⟨.G, 1⟩ :: ms') && s.W == W' then cmp n (i + 1) ms' W'
      else s!"round {i}: differ: zipper W={W'} {repr ms'} / list W={s.W} {repr s.marks}"
    | .halt, .halt => s!"both halt at round {i}"
    | z, .uncovered why => s!"round {i}: list model uncovered ({why}); zipper {showPR z}"
    | z, _ => s!"round {i}: zipper {showPR z}; list model other"

#eval cmp 200 0 [] 5
#eval (steps 17 ⟨blank, blank, .A⟩).map (fun c => cellsOfStart c 12)
