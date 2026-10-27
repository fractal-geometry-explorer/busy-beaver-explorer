import BB6.Round
open BB6

/-! Concrete runs of the proved zipper model `roundZ` (the model of `round_run`), for checking pass maps.
Input lines: `N W t1 p1 t2 p2 …` (marks beyond the gap at 1; t ∈ M W B G). Output: one line per round,
`shape W p1 p2 …`, or `halt` / `uncovered` / `notwf`. -/

def rightOKb (q : Nat) (u : Bool) (W : Nat) : List Mark → Bool
  | [] => q ≤ W && (((W - q) % 2 == 1) == (u == false))
  | m :: ms => q ≤ m.p && (((m.p - q) % 2 == 1) == (u == mval m.t)) && rightOKb (m.p + mlen m.t) (mval m.t) W ms

def tch : MarkT → String | .G => "G" | .M => "M" | .W => "W" | .B => "B"
def ofCh : String → Option MarkT
  | "G" => some .G | "M" => some .M | "W" => some .W | "B" => some .B | _ => none

def parseMarks : List String → Option (List Mark)
  | [] => some []
  | t :: p :: rest => do
      let ty ← ofCh t
      let n ← p.toNat?
      let r ← parseMarks rest
      pure (⟨ty, n⟩ :: r)
  | _ => none

def line (ms : List Mark) (W : Nat) : String :=
  "G" ++ String.join (ms.map (fun m => tch m.t)) ++ " " ++ toString W ++ " " ++
    " ".intercalate (ms.map (fun m => toString m.p))

partial def run (out : IO.FS.Stream) : Nat → List Mark → Nat → IO Unit
  | 0, _, _ => pure ()
  | n + 1, ms, W => do
    match roundZ 100000 [] 1 ms W with
    | .newRound ms' W' => out.putStrLn (line ms' W'); run out n ms' W'
    | .halt => out.putStrLn "halt"
    | _ => out.putStrLn "uncovered"

partial def loop (inp out : IO.FS.Stream) : IO Unit := do
  let l ← inp.getLine
  if l.isEmpty then return
  let ws := (l.trim.splitOn " ").filter (· ≠ "")
  match ws with
  | n :: w :: rest =>
    match n.toNat?, w.toNat?, parseMarks rest with
    | some n, some W, some ms =>
      if rightOKb 4 false W ms then run out n ms W else out.putStrLn "notwf"
    | _, _, _ => out.putStrLn "parse"
  | _ => out.putStrLn "parse"
  out.putStrLn "end"
  out.flush
  loop inp out

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
