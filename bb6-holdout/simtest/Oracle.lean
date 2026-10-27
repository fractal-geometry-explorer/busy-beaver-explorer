import BB6.Round
open BB6

/-! The proved mark model as an oracle for the simulators (`simtest/run.py`).
stdin: one round start per line, `W t p t p ...` (the marks after the gap at 1, t in G M W B).
stdout: for every line, the rounds `roundZ` computes, one per line as `R W t p ...`, ending with `H` (halt),
`U` (uncovered) or `E` (the requested number of rounds reached); the number of rounds is the first argument. -/

def parseT : String → Option MarkT
  | "G" => some .G | "M" => some .M | "W" => some .W | "B" => some .B | _ => none

def tStr : MarkT → String
  | .G => "G" | .M => "M" | .W => "W" | .B => "B"

partial def parseMarks : List String → Option (List Mark)
  | [] => some []
  | t :: p :: rest => do
    let t ← parseT t; let p ← p.toNat?; let ms ← parseMarks rest; pure (⟨t, p⟩ :: ms)
  | _ => none

def showState (ms : List Mark) (W : Nat) : String :=
  String.intercalate " " (s!"R {W}" :: ms.map (fun m => s!"{tStr m.t} {m.p}"))

def runLine (n : Nat) (ws : List String) : List String := Id.run do
  match ws with
  | w :: rest =>
    match w.toNat?, parseMarks rest with
    | some W, some ms =>
      let mut out : List String := []
      let mut cur := (ms, W)
      for _ in [0:n] do
        match roundZ 100000 [] 1 cur.1 cur.2 with
        | .newRound ms' W' => out := showState ms' W' :: out; cur := (ms', W')
        | .halt => return (out.reverse ++ ["H"])
        | _ => return (out.reverse ++ ["U"])
      return (out.reverse ++ ["E"])
    | _, _ => return ["bad input"]
  | [] => return ["bad input"]

partial def loop (n : Nat) (h : IO.FS.Stream) (o : IO.FS.Stream) : IO Unit := do
  let l ← h.getLine
  if l.isEmpty then return
  let ws := (l.trimAsciiEnd.toString.splitOn " ").filter (· ≠ "")
  for s in runLine n ws do o.putStrLn s
  o.putStrLn "."
  o.flush
  loop n h o

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 8
  loop n (← IO.getStdin) (← IO.getStdout)
