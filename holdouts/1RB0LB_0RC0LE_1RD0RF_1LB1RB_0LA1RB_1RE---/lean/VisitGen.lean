import VisitSeg
open VisitLaw
/-- usage: Gen IN OUT K : read "len hex", run K rounds, write "len hex". -/
def main (args : List String) : IO Unit := do
  let [inp, out, ks] := args | throw (IO.userError "usage")
  let txt ← IO.FS.readFile inp
  let [ls, hs] := txt.trimAscii.toString.splitOn " " | throw (IO.userError "bad state")
  let len := ls.toNat!
  let n := hs.foldl (fun a c => 16 * a + (if c.isDigit then c.toNat - 48 else c.toNat - 87)) 0
  match iter ks.toNat! (dec len n) with
  | none => throw (IO.userError "iter failed")
  | some s =>
    let h := hscan fuelR 0 0 (true :: false :: s)
    IO.FS.writeFile out s!"{s.length} {String.ofList (Nat.toDigits 16 (enc s))}\n"
    IO.println s!"len {s.length} nexthalt {h}"
