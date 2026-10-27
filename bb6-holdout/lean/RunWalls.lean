import BB6.Meets
open BB6

/-! # Running the mark model from a three-wall round start (untrusted, for looking)

usage: `lean --run RunWalls.lean a b E R rounds` (after `./check.sh`; walls at a, b, E − R − 1, width E).  Prints each
round's end meetings (`meetsZ`), the next round start's shape, width, right end R and wall/marker positions, and stops
at a halt or an uncovered configuration.  An end meeting at distance ≤ 2 is flagged as a close. -/

def runInfo (ms : List Mark) (W : Nat) (n : Nat) : IO Unit := do
  let mut ms := ms
  let mut W := W
  for i in [0:n] do
    let ds := meetsZ 1000 [] 1 ms W
    if ds.any (· ≤ 2) then IO.println s!"  round {i + 1}: CLOSE, end meetings {ds}"
    match roundZ 1000 [] 1 ms W with
    | .newRound ms' W' =>
      let shape := String.join (ms'.map (fun m => match m.t with | .G => "G" | .M => "M" | .W => "W" | .B => "B"))
      let R := match ms'.getLast? with | some m => (W' : Int) - m.p - 1 | none => 0
      IO.println s!"  after round {i + 1}: G{shape} W={W'} R={R} end meetings {ds} positions {ms'.map (·.p)}"
      ms := ms'; W := W'
    | .halt => IO.println s!"  round {i + 1}: HALT"; return
    | .uncovered => IO.println s!"  round {i + 1}: uncovered (a contact), end meetings {ds}"; return
    | _ => return

def main (args : List String) : IO Unit := do
  let a := args[0]!.toNat!
  let b := args[1]!.toNat!
  let E := args[2]!.toNat!
  let R := args[3]!.toNat!
  let c := E - R - 1
  let L1 : Int := 147 * b + 280 * E - 392 * c - 578
  IO.println s!"walls {a}, {b}, {c}; width {E}; R = {R}; L₁ = {L1}"
  runInfo [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E (args[4]!.toNat!)
