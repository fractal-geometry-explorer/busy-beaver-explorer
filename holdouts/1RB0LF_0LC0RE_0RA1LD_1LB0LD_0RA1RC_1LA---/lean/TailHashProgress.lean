import TailHash

/-! Progress of the Hashlife checker phase by phase (for timing; not a proof).  After `./check_native.sh`:

    lean TailHashProgress.lean -c out/c/Progress.c          # with LEAN_PATH as in check_native.sh
    leanc -O2 out/c/Progress.c $(ls out/c/*.o) -o progress
    WHICH=own N=130 ./progress                             # or WHICH=twin

It prints, after each phase, `X`, the number of runs of the tail, the memo size and the milliseconds so far. -/
open H129771 TM

def loop (which : String) : Nat → Nat → Nat → TM.SX.SSide → Memo → Nat → IO Unit
  | 0, _, _, _, _, _ => pure ()
  | k + 1, i, X, T, M, t0 => do
    match cPhaseF X T M with
    | none => IO.println s!"{which} phase {i + 1} FAILED at X = {X}"
    | some (T', M') =>
      let t ← IO.monoMsNow
      IO.println s!"{which} phase {i + 1} X {f X} runs {T'.length} memo {M'.size} ms {t - t0}"
      (← IO.getStdout).flush
      loop which k (i + 1) (f X) T' M' t0

def main : IO Unit := do
  let t0 ← IO.monoMsNow
  let w ← IO.getEnv "WHICH"
  let n := ((← IO.getEnv "N").getD "130").toNat!
  if w == some "twin" then
    loop "twin" n 0 52 (toS (EX.ofList ws L0twin)) {} t0
  else
    loop "own" n 0 40 (toS (EX.ofList ws L0own)) {} t0
