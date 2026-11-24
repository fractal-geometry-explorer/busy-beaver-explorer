import Fast
open H129887

/-- FNV-1a over the word, front first, `b`/`c`, with the offset basis of `c/wrun.c`'s `whash` (1469598103934665603). -/
def whash (w : List Bool) : UInt64 :=
  w.foldl (fun h x => (h ^^^ (if x then 99 else 98)) * 1099511628211) 1469598103934665603

def word : MS → List Bool
  | ⟨_, .ret _ x w⟩ => x :: w
  | _ => []

def hex16 (u : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 u.toNat)
  String.ofList (List.replicate (16 - s.length) '0') ++ s

partial def loop (dump : Bool) (maxv : Nat) (v : Nat) (s : MS) (k : Nat) (t0 : Nat) : IO Unit := do
  if dump then
    IO.println s!"{v} {k + 2} {hex16 (whash (word s))} {wlen s}"
  else if v &&& (v - 1) == 0 || v == maxv then
    let t ← IO.monoMsNow
    IO.println s!"visit {v} at step {k + 2}: {wlen s} tokens ({(t - t0) / 1000} s)"
    (← IO.getStdout).flush
  if v ≥ maxv then return
  match fvrun 1000000000000 2 s k with
  | some (s', k') => loop dump maxv (v + 1) s' k' t0
  | none => IO.println s!"no next visit after visit {v} (halt or stuck)"

def main (args : List String) : IO Unit := do
  let dump := args.head? == some "dump"
  let maxv := (args.getD 1 "1024").toNat!
  loop dump maxv 1 start 2 (← IO.monoMsNow)
