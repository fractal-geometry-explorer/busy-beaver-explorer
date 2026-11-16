import Zone

/-!
# 1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA: write a state of the zone orbit

Not part of `check.sh`.  After `check.sh` has built `out/`, run from this folder
`LEAN_PATH=$LEANLIB:../../../tools/lean/out:out lean DumpState.lean > state.txt`: one line `t n r Z`, the step
count, the block count, the length of `rest` and the reversed word after the block (head side first), as read by
`c/xs.c` and `c/z1.c` in the folder of `1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA`.  The state is that of
zone step 3 · 10^7 (about two minutes).
-/

open H25821

def dump (k : Nat) : String :=
  match crun k (3, .rt 0 []) with
  | none => "halt"
  | some (t, .rt n Z) => s!"{t} {n} 0 " ++ String.ofList (Z.map (fun b => if b then '1' else '0'))
  | some (t, .raw _) => s!"{t} raw"

#eval IO.println (dump 30000000)
