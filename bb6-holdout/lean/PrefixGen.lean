import BB6.Round
open BB6

/-! # Checkpoints of the run from blank tape (untrusted driver for `thm/gen_prefix.py`)

Runs the mark model from the first round start (`roundStart [] 5`) one round at a time, with `roundZ` as `roundsZ`
does, and writes a checkpoint every `K` rounds and at the first one-marker clean tape whose width is at least
`target`, one per line: `rounds W t p t p …` (the round count, the width, and the marks).  `thm/gen_prefix.py` turns
consecutive checkpoints into theorems that the kernel checks; nothing printed here is trusted.

usage: lean --run PrefixGen.lean target K out.txt -/

def isClean1 : List Mark → Nat → Bool
  | [⟨.M, p⟩], W => p + 2 == W
  | _, _ => false

def tName : MarkT → String
  | .G => "G" | .M => "M" | .W => "W" | .B => "B"

def line (r : Nat) (ms : List Mark) (W : Nat) : String :=
  String.intercalate " " ([toString r, toString W] ++ ms.flatMap (fun m => [tName m.t, toString m.p]))

def main (args : List String) : IO UInt32 := do
  let target := (args.getD 0 "1048576").toNat!
  let K := (args.getD 1 "5000").toNat!
  let out := args.getD 2 "prefix_checkpoints.txt"
  let mut ms : List Mark := []
  let mut W := 5
  let mut r := 0
  let mut lines : Array String := #[line 0 [] 5]
  repeat
    match roundZ 1000 [] 1 ms W with
    | .newRound ms' W' => ms := ms'; W := W'; r := r + 1
    | _ =>
      IO.println s!"round {r + 1} does not end at a round start"
      return 1
    if isClean1 ms W && target ≤ W then
      lines := lines.push (line r ms W)
      break
    if r % K == 0 then lines := lines.push (line r ms W)
  IO.FS.writeFile out (String.intercalate "\n" lines.toList ++ "\n")
  IO.println s!"{r} rounds to the clean tape of width {W}; {lines.size} checkpoints written to {out}"
  return 0
