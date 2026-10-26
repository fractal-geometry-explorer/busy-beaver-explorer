import BB6.SymRound
open BB6 BB6.Sym

/-- The exit start state of a leaf: G 1, W a, W b, W c, width E, every position free; B lower triangular 4 × 4
given by rows; the cone gaps a, b − a, c − b, E − c. -/
def leafStart (_R : Int) (x0 : List Int) (B : List Int) : List SMark × YForm × List YForm :=
  let a : YForm := ⟨x0.getD 0 0, [B.getD 0 0, 0, 0, 0]⟩
  let b : YForm := ⟨x0.getD 1 0, [B.getD 1 0, B.getD 2 0, 0, 0]⟩
  let c : YForm := ⟨x0.getD 2 0, [B.getD 3 0, B.getD 4 0, B.getD 5 0, 0]⟩
  let E : YForm := ⟨x0.getD 3 0, [B.getD 6 0, B.getD 7 0, B.getD 8 0, B.getD 9 0]⟩
  ([⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩], E, [a, b.sub a, c.sub b, E.sub c])

def shapeOf (ss : List SMark) : String := "G" ++ String.join (ss.map (fun m => match m.t with
  | .G => "G" | .M => "M" | .W => "W" | .B => "B"))

/-- Verdict for one leaf: every round decided; for a close leaf the last round is `uncovered` and the earlier
shapes match; for any other leaf every shape matches and every round is covered. -/
def checkLeaf (R : Int) (kind : String) (x0 B : List Int) (rounds : Nat) (shapes : List String) (Γ : Int) : String := Id.run do
  let (ss, W, ts) := leafStart R x0 B
  let mut cur := ss
  let mut cw := W
  for i in [0:rounds] do
    match symRoundZ ts Γ 1000 [] (YForm.const 1) cur cw with
    | some (.newRound ss' W') =>
      if shapeOf ss' != shapes.getD i "" then return s!"shape mismatch at round {i+1}: {shapeOf ss'} vs {shapes.getD i ""}"
      cur := ss'; cw := W'
    | some .uncovered => return s!"uncovered at round {i+1}"
    | some .halt => return s!"halt at round {i+1}"
    | some (.gap _ _ _ _) => return "gap?"
    | none => return s!"undecided at round {i+1}"
  return "ok"

def parseInts (s : String) : List Int := (s.splitOn ",").map (fun t => t.trimAscii.toString.toInt?.getD 0)

def field (ws : List String) (key : String) : String :=
  match ws.find? (·.startsWith key) with
  | some w => (w.drop key.length).toString
  | none => ""

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "../cert/exit_leaves.txt"
  let limit := (args.getD 1 "1000000000").toNat!
  let Γ : Int := (args.getD 2 "256").toInt!
  let lines ← IO.FS.lines path
  let mut n := 0
  let mut ok := 0
  let mut bad : List String := []
  let mut kinds : List (String × Nat) := []
  for line in lines do
    if n ≥ limit then break
    if !(line.startsWith "X ") then continue
    let parts := line.splitOn " | "
    let ws := (parts.getD 0 "").splitOn " "
    let shapes := ((parts.getD 1 "").splitOn " ").filter (· != "")
    let R : Int := 0
    let kind := ws.getD 2 ""
    let x0 := parseInts (field ws "x0=")
    let B := parseInts (field ws "B=")
    let rounds := (field ws "rounds=").toNat!
    let v := checkLeaf R kind x0 B rounds shapes Γ
    n := n + 1
    if v == "ok" then ok := ok + 1
    else if bad.length < 20 then bad := bad ++ [s!"{line.take 80} -> {v}"]
    kinds := match kinds.find? (·.1 == kind ++ ":" ++ v) with
      | some _ => kinds.map (fun p => if p.1 == kind ++ ":" ++ v then (p.1, p.2 + 1) else p)
      | none => kinds ++ [(kind ++ ":" ++ v, 1)]
  IO.println s!"leaves checked {n}; ok {ok}; Γ = {Γ}"
  for (k, c) in kinds do IO.println s!"  {k}: {c}"
  for b in bad do IO.println b
