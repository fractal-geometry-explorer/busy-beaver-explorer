"""The branch table of 1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB: every exit of every phase form that the run takes
through its first 10^15 steps, proved in Lean for all sizes.

usage: python3 holdouts/1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB/py/branch.py     writes lean/Branch.lean
                                                                                   (needs lean/Cycle.lean, Phase.lean)

Each rule is a symbolic run (`bbtools.symtm.prove`) from a form with symbolic counts to the first visit that
matches the target form, followed by the proof that its end tape, as the run writes it, is the stated form
(`py/tapeeq.py`).  `RULES` lists them as (start form, start arguments, target form, target arguments, steps); the
step counts and target arguments were found by running the same symbolic simulation (`py/macro.py` replays them).
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.symtm import rules_file, parse_lin  # noqa: E402
from tapeeq import defn, rule  # noqa: E402

NS = "H113677"
J0 = "0 0 0 0 1 0 0 0 0 0 1 0 0 0"
J1 = "0 0 1 0 0 0 0 0 1 0 0 0 1 0 1 0^inf"
LG = "0 1 1 0 1 0 1 0 1 0 1 0 1 0 0 1"          # the fixed glue left of the first run in a two-run right phase
LG3 = "1 1 1 1 1 1 0 1 1 1 1 1 1 0 1 1 1 0 0 1"  # ... in a three-run right phase

FORMS = {
    # defined in Cycle.lean / Phase.lean
    "O": lambda a, b, c: f"0^inf A> 0 0 0 0 0 0 0 (1000)^{a} (10)^{b} (00001000001000)^{c} 1 0 1 0^inf",
    "S1": lambda a, b, c: f"0^inf A> 0 0 0 0 0 0 0 (1000)^{a} {J0} (10)^{b} (00100000100000)^{c} " + J1,
    "T2": lambda a, x, y, c: (f"0^inf A> 0 0 0 0 0 0 0 (1000)^{a} {J0} (10)^{x} 0 (01)^{y} (00000001000001)^{c} "
                              "0 0 0 1 0 1 0^inf"),
    "T3": lambda a, x, d, y, z, c: (f"0^inf A> 0 0 0 0 0 0 0 (1000)^{a} (10)^{x} (0010)^{d} (10)^{y} {J0} (10)^{z} "
                                    f"(00100000100000)^{c} " + J1),
    "RF": lambda a, k, m: f"0^inf (1110)^{a} (1111110)^{k} 1 1 1 0 0 1 (10)^{m} 1 E> 0^inf",
    "RF2": lambda a, q, m: f"0^inf (1110)^{a} (11111101111110)^{q} 1 1 1 1 1 1 0 1 1 1 0 0 1 (10)^{m} 1 E> 0^inf",
    "EF": lambda a, q: (f"0^inf E> 0 0 0 0 0 (0001)^{a} (00000100000001)^{q} 0 0 0 0 0 1 0 0 0 0 0 0 0 1 0 0 0 0 0 1 "
                        "0 0 0 1 0 1 0^inf"),
    # new here
    "U3": lambda a, x, y, z, c: (f"0^inf A> 0 0 0 0 0 0 0 (1000)^{a} {J0} (10)^{x} 0 (01)^{y} 0 {J0} (10)^{z} "
                                 f"(00100000100000)^{c} " + J1),
    "RG": lambda a, x, n, m: f"0^inf (1110)^{a} {LG} (10)^{x} (1111011)^{n} 1 0 0 1 (10)^{m} 1 E> 0^inf",
    "RG2": lambda a, x, q, m: f"0^inf (1110)^{a} {LG} (10)^{x} (11110111111011)^{q} 1 0 0 1 (10)^{m} 1 E> 0^inf",
    "RG3": lambda a, x, y, n, m: (f"0^inf (1110)^{a} {LG3} (10)^{x} 1 1 1 0 0 1 (10)^{y} (1111011)^{n} 1 0 0 1 "
                                  f"(10)^{m} 1 E> 0^inf"),
    "RG3p": lambda a, x, y, q, m: (f"0^inf (1110)^{a} {LG3} (10)^{x} 1 1 1 0 0 1 (10)^{y} (11110111111011)^{q} "
                                   f"1 0 0 1 (10)^{m} 1 E> 0^inf"),
}
NEW = {
    "U3": (["a", "x", "y", "z", "c"], "A round-trip visit with three runs of `10`, the middle one frozen."),
    "RG": (["a", "x", "n", "m"], "A right-end visit in a right phase with two runs."),
    "RG2": (["a", "x", "q", "m"], "`RG a x (2q) m` with the run of `1111011` in pairs."),
    "RG3": (["a", "x", "y", "n", "m"], "A right-end visit in a right phase with three runs."),
    "RG3p": (["a", "x", "y", "q", "m"], "`RG3 a x y (2q) m` with the run of `1111011` in pairs."),
}

# name: (start form, start args, target form, target args, steps, doc)
RULES = [
    ("eentry", "EF", ["a+7", "q+5"], "T3", ["5", "14", "a", "8", "7", "q+2"], "120*a+2501",
     "Entry into an even round-trip phase: `EF (a+7) (q+5)` -> `T3 5 14 a 8 7 (q+2)`."),
    ("texit0", "T3", ["a", "x+5", "0", "y+2", "z+2", "c+1"], "T2", ["a+1", "x+y+6", "z+6", "c+1"], None,
     "Exit of the 5-visit cycle with no `0010` left: the first two runs merge."),
    ("texit1", "T3", ["a", "x+6", "1", "y+5", "z+6", "c+2"], "U3", ["a+2", "x+6", "y+6", "z+11", "c"], None,
     "Exit with one `0010` left: three runs, the middle one frozen from now on."),
    ("texit2", "T3", ["a", "x+6", "2", "y+5", "z+6", "c+2"], "U3", ["a+2", "x+8", "y+6", "z+11", "c"], None,
     "Exit with two `0010` left: three runs, the middle one frozen."),
    ("texit3", "T3", ["a", "x+6", "3", "y+5", "z+6", "c+3"], "T2", ["a+5", "x+y+21", "z+15", "c+1"], None,
     "Exit with three `0010` left: the first two runs merge."),
    ("texit4", "T3", ["a", "x+6", "4", "y+5", "z+6", "c+3"], "T2", ["a+5", "x+y+23", "z+15", "c+1"], None,
     "Exit with four `0010` left: the first two runs merge."),
    ("ucyc", "U3", ["a", "x+2", "y+6", "z+6", "c+2"], "U3", ["a+3", "x+9", "y+6", "z+11", "c"], None,
     "The 4-visit cycle with three runs: (a, x, y, z, c+2) -> (a+3, x+7, y, z+5, c)."),
    ("t2exit0", "T2", ["a", "x+2", "y+10", "0"], "RG", ["a+3", "x+1", "4", "y+6"], None,
     "The end of a two-run round-trip phase with no 14-cell word left: into a right phase."),
    ("t2exit1", "T2", ["a", "x+2", "y+12", "1"], "RG", ["a+3", "x+1", "5", "y+7"], None,
     "The end of a two-run round-trip phase with one 14-cell word left."),
    ("gcyc", "RG", ["a", "x", "n", "m+2"], "RG", ["a", "x", "n+1", "m+1"], None,
     "The two-run right-phase cycle: one `10` becomes one `1111011`."),
    ("gend", "RG2", ["a+2", "x", "q", "1"], "O", ["a+1", "x+9", "q+1"], None,
     "The end of a two-run right phase with an even run of `1111011`: an odd-type round-trip phase."),
    ("uexit0", "U3", ["a", "x+2", "y+6", "z+10", "0"], "RG3", ["a+3", "x+7", "y+4", "4", "z+10"], None,
     "The end of a three-run round-trip phase with no 14-cell word left."),
    ("uexit1", "U3", ["a", "x+2", "y+6", "z+12", "1"], "RG3", ["a+3", "x+7", "y+4", "5", "z+11"], None,
     "The end of a three-run round-trip phase with one 14-cell word left."),
    ("g3cyc", "RG3", ["a", "x", "y", "n", "m+2"], "RG3", ["a", "x", "y", "n+1", "m+1"], None,
     "The three-run right-phase cycle."),
    ("g3end", "RG3p", ["a", "x", "y+4", "q+2", "1"], "T2", ["a+3", "x+9", "y+10", "q+1"], None,
     "The end of a three-run right phase with an even run of `1111011`: a two-run round-trip phase."),
    ("sexit0", "S1", ["a", "b+3", "0"], "RF", ["a+3", "4", "b+10"], None,
     "The last turn of an odd-type round-trip phase with no 14-cell word left: into a right phase."),
]


def term(e):
    t = parse_lin(e).lean() if not e.isdigit() else e
    return t if t.replace("_", "").isalnum() else f"({t})"


DOC = """# The branch table: every exit the run takes through its first 10^15 steps

Forms (the ones of `Cycle.lean` and `Phase.lean`, and):
`U3 a x y z c` = `0^inf A> 0^7 (1000)^a J0 (10)^x 0 (01)^y 0 J0 (10)^z (00100000100000)^c J` (three runs, the middle
one frozen), `RG a x n m` = `0^inf (1110)^a 0110101010101001 (10)^x (1111011)^n 1001 (10)^m 1 E> 0^inf` (right phase
after a two-run round trip), `RG3 a x y n m` = `0^inf (1110)^a 11111101111110111001 (10)^x 111001 (10)^y (1111011)^n
1001 (10)^m 1 E> 0^inf` (right phase after a three-run round trip); `RG2`, `RG3p` write the run of `1111011` in pairs.

Rules (each for all values of the variables): the even phase's entry `eentry`; the five exits `texit0`..`texit4` of
the 5-visit cycle by how many `0010` are left (0, 3, 4 merge two runs into `T2`; 1, 2 leave three runs, `U3`); the
three-run cycle `ucyc`; the exits of the two- and three-run round trips into right phases (`t2exit0/1`,
`uexit0/1`, by the parity of the 14-cell words left); the right-phase cycles `gcyc`, `g3cyc`; their ends with an
even run of `1111011` (`gend`, `g3end`, via `gend'`, `g3end'`); and the exit `sexit0` of the 4-visit cycle with
no 14-cell word left.  `*_iter` apply the cycles k times.

Generated by `py/branch.py`."""

ITER = """/-- `ucyc` k times. -/
theorem ucyc_iter (k : Nat) : ∀ a x y z c : Nat, ∃ n,
    steps n (U3 a (x + 2) (y + 6) (z + 6) (c + 2 * k)) =
      some (U3 (a + 3 * k) (x + 2 + 7 * k) (y + 6) (z + 6 + 5 * k) c) := by
  induction k with
  | zero => intro a x y z c; exact ⟨0, by simp⟩
  | succ k ih =>
    intro a x y z c
    obtain ⟨n, hn⟩ := ih (a + 3) (x + 7) y (z + 5) c
    have h := ucyc a (c + 2 * k) x y z
    rw [show x + 9 = x + 7 + 2 by omega, show z + 11 = z + 5 + 6 by omega] at h
    rw [show c + 2 * (k + 1) = c + 2 * k + 2 by omega, show a + 3 * (k + 1) = a + 3 + 3 * k by omega,
      show x + 2 + 7 * (k + 1) = x + 7 + 2 + 7 * k by omega, show z + 6 + 5 * (k + 1) = z + 5 + 6 + 5 * k by omega]
    exact ⟨_, steps_seq trans h hn⟩

/-- `gcyc` t times. -/
theorem gcyc_iter (t : Nat) : ∀ a x n m : Nat, ∃ s,
    steps s (RG a x n (m + 1 + t)) = some (RG a x (n + t) (m + 1)) := by
  induction t with
  | zero => intro a x n m; exact ⟨0, by simp⟩
  | succ t ih =>
    intro a x n m
    obtain ⟨s, hs⟩ := ih a x (n + 1) m
    have h := gcyc a (m + t) n x
    rw [show m + t + 1 = m + 1 + t by omega] at h
    rw [show m + 1 + (t + 1) = m + t + 2 by omega, show n + (t + 1) = n + 1 + t by omega]
    exact ⟨_, steps_seq trans h hs⟩

/-- `g3cyc` t times. -/
theorem g3cyc_iter (t : Nat) : ∀ a x y n m : Nat, ∃ s,
    steps s (RG3 a x y n (m + 1 + t)) = some (RG3 a x y (n + t) (m + 1)) := by
  induction t with
  | zero => intro a x y n m; exact ⟨0, by simp⟩
  | succ t ih =>
    intro a x y n m
    obtain ⟨s, hs⟩ := ih a x y (n + 1) m
    have h := g3cyc a (m + t) n x y
    rw [show m + t + 1 = m + 1 + t by omega] at h
    rw [show m + 1 + (t + 1) = m + t + 2 by omega, show n + (t + 1) = n + 1 + t by omega]
    exact ⟨_, steps_seq trans h hs⟩

/-- The end of a two-run right phase whose run of `1111011` has even length 2q. -/
theorem gend' (a x q : Nat) : ∃ n, steps n (RG (a + 2) x (2 * q) 1) = some (O (a + 1) (x + 9) (q + 1)) := by
  have e : RG (a + 2) x (2 * q) 1 = RG2 (a + 2) x q 1 := by
    simp only [RG, RG2, rep_double, List.cons_append, List.nil_append]
  rw [e]
  exact ⟨_, gend a q x⟩

/-- The end of a three-run right phase whose run of `1111011` has even length 2q+4. -/
theorem g3end' (a x y q : Nat) :
    ∃ n, steps n (RG3 a x (y + 4) (2 * q + 4) 1) = some (T2 (a + 3) (x + 9) (y + 10) (q + 1)) := by
  have e : RG3 a x (y + 4) (2 * q + 4) 1 = RG3p a x (y + 4) (q + 2) 1 := by
    rw [show 2 * q + 4 = 2 * (q + 2) by omega]
    simp only [RG3, RG3p, rep_double, List.cons_append, List.nil_append]
  rw [e]
  exact ⟨_, g3end a q x y⟩
"""


def main():
    parts = ["set_option maxRecDepth 100000\n"]
    for f, (args, doc) in NEW.items():
        parts.append(defn(f, args, FORMS[f], doc))
    for name, f, args, tf, targs, _steps, doc in RULES:
        vs = sorted({v for a in args for v in parse_lin(a).c})
        lhs = f"{f} " + " ".join(term(a) for a in args)
        rhs = f"{tf} " + " ".join(term(a) for a in targs)
        parts += rule(name, FORMS[f](*args), FORMS[tf](*targs), vs, lhs, rhs, doc)
    parts.append(ITER)
    with open(os.path.join(HERE, "..", "lean", "Branch.lean"), "w") as fh:
        fh.write(rules_file("Phase", NS, parts, DOC))


if __name__ == "__main__":
    main()
