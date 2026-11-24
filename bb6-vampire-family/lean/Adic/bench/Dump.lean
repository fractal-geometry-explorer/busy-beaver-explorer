import Adic.Machines

/-! Writes the three tables as literals (`out/bench/Tabs.lean`), for the compiled benchmark `Bench.lean`. -/

open Adic

def show1 : Res → String
  | .go c d => s!"(.go {c} {d})"
  | .halt => ".halt"
  | .out => ".out"

def dump (nm : String) (t : Tab) : String :=
  s!"def {nm} : Tab := #[" ++ ", ".intercalate (t.toList.map show1) ++ "]\n"

#eval IO.FS.writeFile "out/bench/Tabs.lean"
  ("import Adic.Basic\nopen Adic\n" ++ dump "tLC" VLC.Adic.tab ++ dump "tLA" VLA.Adic.tab ++ dump "tRB" VRB.Adic.tab)
