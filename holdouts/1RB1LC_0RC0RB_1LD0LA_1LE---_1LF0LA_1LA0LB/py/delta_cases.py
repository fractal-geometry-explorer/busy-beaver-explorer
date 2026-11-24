"""Write a Lean file that evaluates the walk of lean/DeltaBound.lean on random counters and compares it with
`walk` of py/map.py (pairs read, next digit, delta).  Its last two outputs should be `true` and the number of cases.

usage: python3 py/delta_cases.py T > /tmp/DeltaCheck.lean && (cd lean && LEAN_PATH=$LEANLIB:out:../../../tools/lean/out lean /tmp/DeltaCheck.lean)
       (after lean/check.sh has built lean/out/DeltaBound.olean)
"""
import os, sys, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import map as Mp

T = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
random.seed(5)
cases = []
for _ in range(T):
    B = random.choice([6, 10, 20, 60, 200]); U = random.getrandbits(B) | (1 << B); h = random.randint(0, 1)
    j, b, d = Mp.walk(h, U)
    if j < Mp.OUT: cases.append((h, U, j, b, d))
tf = lambda x: "true" if x else "false"
print("""import DeltaBound
open H49767Delta
def pairsOf : Nat → Nat → List (Bool × Bool)
  | 0, _ => []
  | f+1, U => if U = 0 then [] else (U % 2 = 1, (U / 2) % 2 = 1) :: pairsOf f (U / 4)
set_option maxRecDepth 100000 in
def cases : List (Bool × Nat × Nat × Bool × Nat) := [""" + ",\n ".join(
    f"({tf(h)}, {U}, {j}, {tf(b)}, {d})" for h, U, j, b, d in cases) + """]
def ok : Bool := cases.all fun (h, U, j, b, d) =>
  match walk h (pairsOf 400 U) with
  | some (i, b', d') => 2 * i + 1 == j && b' == b && d' == d
  | none => false
#eval ok
#eval cases.length""")
