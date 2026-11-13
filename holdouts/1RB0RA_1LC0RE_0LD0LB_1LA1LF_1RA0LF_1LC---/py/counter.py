"""Generate lean/Counter.lean for 1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---: the ternary counter's increment.

The eight pieces of a trip (the head's round trip from the left end back to it) are proved along the symbolic run of
tools/py/bbtools/symtm.py (single steps by `rfl`, shift rules by TM.cross_r/cross_l, re-bracketing by
TM.rep_rotate); the hand-written part at the end chains them, by induction over the digits a carry runs through,
into one theorem per kind of trip, for every carry depth.

Words below are written left to right; a run of alternating cells is written with the repeat `(0101)^n` or
`(1010)^n` and a few literal cells.  Notation of the README: digit 0 = runs (r0, r1) at the left end, digit k >= 1 =
runs (x_k, y_k); residues mod 4.

usage (from the repo root): python3 holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/counter.py > holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/lean/Counter.lean
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.symtm import prove  # noqa: E402

M = "1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---"
NS = next(l.split()[1] for l in open(os.path.join(HERE, "..", "lean", "Machine.lean")) if l.startswith("namespace "))

PIECES = [
    ("inc0",
     "0^inf A> (0101)^a+1 (1010)^b+1 101 10 R",
     "0^inf A> 0 1 0 1 0 (1010)^a 1 1 0 1 0 (1010)^b+1 1 0 0 R",
     "Digit 0 goes 0 -> 1: runs (r0, r1) = (4a+4, 4b+7), digit 1 starting `1 0`.  One trip: r0 + 2, r1 + 3, and the "
     "first cell of digit 1 is taken (x1 - 1)."),
    ("inc1",
     "0^inf A> (0101)^a+1 01 (1010)^b+1 10 R",
     "0^inf A> 0 1 0 1 0 (1010)^a+1 1 0 0 1 0 (1010)^b 1 0 R",
     "Digit 0 goes 1 -> 2: (r0, r1) = (4a+6, 4b+6).  One trip: r0 + 5, r1 - 1; the rest of the tape is not read."),
    ("out0",
     "0^inf A> (0101)^a+1 010 (0101)^b+1 0 R",
     "0^inf (1010)^a+1 1 0 1 (1010)^b+1 1 B> R",
     "Digit 0 at 2 carries: (r0, r1) = (4a+7, 4b+5).  Going right, A flips both runs and arrives in B at digit 1."),
    ("carry",
     "L 1 (1010)^e+1 1 B> (0101)^c+2 0 (0101)^d+1 0 R",
     "L (0101)^e+1 0 1 0 0 (1010)^c+1 1 0 1 (1010)^d+1 1 B> R",
     "A carry passes digit k at 2: (x, y) = (4c+9, 4d+5).  B bounces back over the flipped previous run, then crosses "
     "the digit and arrives in B at digit k+1."),
    ("absorb1",
     "L 1 (1010)^e+1 1 B> (0101)^c+1 (1010)^d+1 10 R",
     "L B> 0 0 1 0 (1010)^e 1 1 0 1 0 (1010)^c 1 0 0 1 0 (1010)^d 1 0 R",
     "A carry stops at digit k at 1: (x, y) = (4c+4, 4d+6).  The head turns and heads home in B."),
    ("absorb0",
     "L 1 (1010)^e+1 1 B> (0101)^c+1 01 (1010)^d+1 101 10 R",
     "L B> 0 0 1 0 (1010)^e 1 1 0 1 0 (1010)^c 1 1 0 1 0 (1010)^d+1 1 0 0 R",
     "A carry stops at digit k at 0: (x, y) = (4c+6, 4d+7), digit k+1 starting `1 0`; its first cell is taken."),
    ("home",
     "L (0101)^e+1 0 1 0 0 (1010)^c+1 1 0 B> 0 R",
     "L B> 0 0 1 0 (1010)^e 1 1 0 1 0 1 0 (1010)^c 1 1 0 1 R",
     "Going home, B crosses a digit the carry went through."),
    ("home0",
     "0^inf (1010)^a+1 1 0 B> 0 R",
     "0^inf A> 0 1 0 1 0 1 0 (1010)^a 1 1 0 1 R",
     "Going home, B crosses digit 0 and the left end grows by four cells; A starts the next trip."),
]

TAIL = r'''
/-! ## Chaining the pieces: one theorem per kind of trip, every carry depth

The left stream after the carry has passed digits `1..k` and the right stream of the digits still ahead, nearest
cell first as in `TM.Tape`.  `cin e L` is `L 1 (1010)^(e+1) 1` (the head has just arrived at a digit in B),
`kblk e c L` is `L (0101)^(e+1) 0 1 0 0 (1010)^(c+1) 1 0` (a digit the carry has passed), `dig2 c d R` is a digit at
2, `(0101)^(c+2) 0 (0101)^(d+1) 0 R`. -/

def cin (e : Nat) (L : Tape) : Tape := cons true (rep (e + 1) [false, true, false, true] (cons true L))

def kblk (e c : Nat) (L : Tape) : Tape :=
  cons false (cons true (rep (c + 1) [false, true, false, true] (cons false (cons false (cons true (cons false
    (rep (e + 1) [true, false, true, false] L)))))))

def dig2 (c d : Nat) (R : Tape) : Tape :=
  rep (c + 2) [false, true, false, true] (cons false (rep (d + 1) [false, true, false, true] (cons false R)))

/-- The digits at 2 that a carry passes, nearest first, as `(c, d)` with `(x, y) = (4c+9, 4d+5)`. -/
def digs : List (Nat × Nat) → Tape → Tape
  | [], R => R
  | (c, d) :: ds, R => dig2 c d (digs ds R)

/-- The left stream once the carry has passed the digits `ds` (the first entered with `cin e`). -/
def cout : Nat → List (Nat × Nat) → Tape → Tape
  | _, [], L => L
  | e, (c, d) :: ds, L => cout d ds (kblk e c L)

def clast : Nat → List (Nat × Nat) → Nat
  | e, [] => e
  | _, (_, d) :: ds => clast d ds

def ccost : Nat → List (Nat × Nat) → Nat
  | _, [] => 0
  | e, (c, d) :: ds => (4 * c + 4 * d + 8 * e + 26) + ccost d ds

/-- The carry runs through every digit of `ds` (each at 2) and arrives at the digit after them. -/
theorem carry_chain : ∀ (ds : List (Nat × Nat)) (e : Nat) (L R : Tape),
    steps (ccost e ds) ⟨cin e L, digs ds R, .B⟩ = some ⟨cin (clast e ds) (cout e ds L), R, .B⟩
  | [], e, L, R => rfl
  | (c, d) :: ds, e, L, R => by
    have h1 := carry c d e L (digs ds R)
    have h2 := carry_chain ds d (kblk e c L) R
    exact steps_seq trans h1 h2

/-- What going home leaves behind each passed digit (the right stream after it). -/
def wout (e c : Nat) (R : Tape) : Tape :=
  cons false (cons true (cons false (rep e [true, false, true, false] (cons true (cons true (cons false (cons true
    (cons false (cons true (cons false (rep c [true, false, true, false] (cons true (cons true (cons false
    (cons true R)))))))))))))))

def rout : Nat → List (Nat × Nat) → Tape → Tape
  | _, [], R => R
  | e, (c, d) :: ds, R => wout e c (rout d ds R)

def rcost : Nat → List (Nat × Nat) → Nat
  | _, [] => 0
  | e, (c, d) :: ds => rcost d ds + (4 * c + 4 * e + 14)

/-- Going home over every digit the carry passed. -/
theorem home_chain : ∀ (ds : List (Nat × Nat)) (e : Nat) (L R : Tape),
    steps (rcost e ds) ⟨cout e ds L, cons false R, .B⟩ = some ⟨L, cons false (rout e ds R), .B⟩
  | [], e, L, R => rfl
  | (c, d) :: ds, e, L, R => by
    have h1 := home_chain ds d (kblk e c L) R
    have h2 := home c e L (rout d ds R)
    exact steps_seq trans h1 h2

/-- Digit 0 at 2 as the trip finds it: `(0101)^(a+1) 010 (0101)^(b+1) 0`, i.e. `(r0, r1) = (4a+7, 4b+5)`. -/
def d0two (a b : Nat) (R : Tape) : Tape :=
  rep (a + 1) [false, true, false, true] (cons false (cons true (cons false
    (rep (b + 1) [false, true, false, true] (cons false R)))))

/-- The left stream `0^inf (1010)^(a+1) 1 0` that digit 0 leaves while the carry is out. -/
def lhome (a : Nat) : Tape := cons false (cons true (rep (a + 1) [false, true, false, true] blank))

'''


B = {"0": "false", "1": "true"}
W = {"0101": "[false, true, false, true]", "1010": "[true, false, true, false]"}


def term(toks, rest):
    """A right stream from tokens: '0'/'1' cells, ('0101', n) repeats, ('raw', text) terms that take the rest."""
    out = rest
    for t in reversed(toks):
        if isinstance(t, str):
            for ch in reversed(t):
                out = f"cons {B[ch]} ({out})"
        elif t[0] == "raw":
            out = t[1].replace("#", f"({out})")
        else:
            out = f"rep ({t[1]}) {W[t[0]]} ({out})"
    return out


def trip(name, doc, absorb, cost_abs, digit_toks, after_toks):
    """digit_toks: the stopping digit (and the cells it takes from the next one) before R; after_toks: what the
    absorb piece leaves to the right of the head after its first cell."""
    start = term([("raw", "d0two a b #"), ("raw", "digs ds #")] + digit_toks, "R")
    mid_r = term(after_toks, "R")             # right of `B> 0` after the absorb piece
    home_r = f"rout b ds ({mid_r})"
    end = term(["0101010", ("1010", "a"), "1101"], home_r)
    cost = f"(4 * a + 4 * b + 12) + ccost b ds + ({cost_abs}) + rcost b ds + (4 * a + 10)"
    rest_after_out = term(digit_toks, "R")
    return f"""/-- {doc} -/
theorem {name} (a b c d : Nat) (ds : List (Nat × Nat)) (R : Tape) :
    steps ({cost}) ⟨blank, {start}, .A⟩ = some ⟨blank, {end}, .A⟩ := by
  have h1 := out0 a b (digs ds ({rest_after_out}))
  have h2 := carry_chain ds b (lhome a) ({rest_after_out})
  have h3 := {absorb} c d (clast b ds) (cout b ds (lhome a)) R
  have h4 := home_chain ds b (lhome a) ({mid_r})
  have h5 := home0 a ({home_r})
  exact steps_congr trans (by omega) (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 h5))))
"""


TRIPS = [
    ("trip_stop1",
     "A carry that stops at a digit at 1: digit 0 at 2, the digits `ds` at 2, then a digit `(x, y) = (4c+4, 4d+6)`. "
     "Every carry depth `ds.length + 1` at once.",
     "absorb1", "8 * c + 12 * clast b ds + 26",
     [("0101", "c + 1"), ("1010", "d + 1"), "10"],
     ["010", ("1010", "clast b ds"), "11010", ("1010", "c"), "10010", ("1010", "d"), "10"]),
    ("trip_stop0",
     "A carry that stops at a digit at 0: digit 0 at 2, the digits `ds` at 2, then a digit `(x, y) = (4c+6, 4d+7)` "
     "and the next digit starting `1 0` (its first cell is taken).  Every carry depth at once.",
     "absorb0", "8 * c + 8 * d + 12 * clast b ds + 44",
     [("0101", "c + 1"), "01", ("1010", "d + 1"), "101", "10"],
     ["010", ("1010", "clast b ds"), "11010", ("1010", "c"), "11010", ("1010", "d + 1"), "100"]),
]


def main():
    out = ["import Machine", "",
           f"/-! The ternary counter of {M}, generated by `py/counter.py`; do not edit by hand. -/", "",
           f"namespace {NS}", "", "open TM", ""]
    for name, a, b, doc in PIECES:
        th, _ = prove(M, name, a, b, doc=doc, rotate=True, count_first=True, max_seg=40)
        out.append(th)
        out.append("")
    out.append(TAIL)
    for t in TRIPS:
        out.append(trip(*t))
    out.append(f"end {NS}")
    sys.stdout.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
