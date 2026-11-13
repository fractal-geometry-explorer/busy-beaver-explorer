"""Write lean/Counter.lean for one machine of the 1RB1LA_1LC1RD_1LA0LC_1RE0RB_ family: the two binary counters as
theorems for all values.

The tape at a pass start is read as two numbers written in binary, least significant bit next to the head:
  left  (head-outward): a 0 bit is `1 1`, a 1 bit is `1 0`                (`Lbits`)
  right (head-outward): a 0 bit is `0^P`, a 1 bit is `0^(P-1) 1`           (`Rbits`; P = 3 for 1a/1b, 5 for 1c/1d)
so a block 1^(2a+1) followed by a 0 on the left is a 1 bit after a zero bits, and a gap 0^(P d + P - 1) followed by a
1 on the right is a 1 bit after d zero bits.  One pass pair (an odd pass and the even pass after it) subtracts one
from the left number and adds one to the right number (`cyc3`, `cyc5a`, `cyc5b`, from the symbolic rules `pair3`,
`pair5a`, `pair5b` proved by `bbtools.symtm`), and by induction a whole countdown follows (`run3`, `run5`).

Usage (from the repository root):
  python3 holdouts/<1a folder>/py/gen_counter.py MACHINE NAMESPACE > holdouts/MACHINE/lean/Counter.lean"""
import os
import sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.symtm import prove


def pair_rules(M, P):
    z1 = "0" * (P - 1) + "1"
    z0 = " ".join("0" * P)
    zz = "0" * P
    # one cut + one decrement: (z1)^j z0 X  ->  0 (zz)^j 0^(P-2) 1 X   (the j small gaps and the first zero bit)
    tail_in = f"({z1})^j {z0} X"
    tail_out = f"0 ({zz})^j {' '.join('0' * (P - 2))} 1 X"
    return [
        ("pair3", f"L 1^c+1 0 (11)^a 1 A> 0 1^3 {tail_in}", f"L 1^c+3 (01)^a A> 0 1 1 1 {tail_out}",
         "Mode 3, one pass pair: `P3` pops the top block 1^(2a+1), the even pass pushes a single 1s and adds two 1s to the block below; on the right the j small gaps and the first long gap are cut and the new first gap shrinks by one."),
        ("pair5a", f"L 0 1 (11)^a A> 0 1^5 {tail_in}", f"L A> 0 (11)^a 1^7 {tail_out}",
         "Mode 5, first pass pair: the top block 1^(2a+1) grows by two and is popped onto the top block, which becomes 1^(2a+7)."),
        ("pair5b", f"L 1^c+1 A> 0 (11)^a 1^7 {tail_in}", f"L 1^c+3 (01)^a A> 0 1^5 {tail_out}",
         "Mode 5, second pass pair: the top block 1^(2a+7) pushes a single 1s and adds two 1s to the block below; the top block is 1^5 again."),
    ]


TEMPLATE = r'''
/-! ## The two counters

`Lbits w Y` writes the bits `w` (least significant first) head-outward on the left: a 0 bit is `1 1`, a 1 bit is
`1 0`.  So `Lbits (0^a 1 w) Y` starts with the block `1^(2a+1) 0`.  `Rbits v X` writes bits on the right: a 0 bit is
`Z0 = 0^P`, a 1 bit is `Z1 = 0^(P-1) 1`.  `bitsN n x` is the n low bits of x.  Leading zero bits are `1 1` pairs
that merge with the block below (the floor) on the left, and runs of `0^P` that merge with the gap above on the
right, so a fixed width costs nothing: the same tape is described for every width that holds the number. -/

abbrev T : List Bool := [true]
abbrev Z0 : List Bool := __Z0__
abbrev Z1 : List Bool := __Z1__

def Lbits : List Bool → Tape → Tape
  | [], Y => Y
  | false :: w, Y => cons true (cons true (Lbits w Y))
  | true :: w, Y => cons true (cons false (Lbits w Y))

def Rbits : List Bool → Tape → Tape
  | [], X => X
  | false :: v, X => app Z0 (Rbits v X)
  | true :: v, X => app Z1 (Rbits v X)

theorem Lbits_zeros (a : Nat) (w : List Bool) (Y : Tape) :
    Lbits (List.replicate a false ++ w) Y = rep a [true, true] (Lbits w Y) := by
  induction a with
  | zero => rfl
  | succ a ih => rw [List.replicate_succ, List.cons_append, Lbits, ih]; rfl

theorem Lbits_ones (a : Nat) (w : List Bool) (Y : Tape) :
    Lbits (List.replicate a true ++ w) Y = rep a [true, false] (Lbits w Y) := by
  induction a with
  | zero => rfl
  | succ a ih => rw [List.replicate_succ, List.cons_append, Lbits, ih]; rfl

theorem Rbits_ones (j : Nat) (v : List Bool) (X : Tape) :
    Rbits (List.replicate j true ++ v) X = rep j Z1 (Rbits v X) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ, List.cons_append, Rbits, ih]; rfl

theorem Rbits_zeros (j : Nat) (v : List Bool) (X : Tape) :
    Rbits (List.replicate j false ++ v) X = rep j Z0 (Rbits v X) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ, List.cons_append, Rbits, ih]; rfl

theorem Lbits_head (w : List Bool) (Y : Tape) : ∃ Y', Lbits w (cons true Y) = cons true Y' := by
  cases w with
  | nil => exact ⟨Y, rfl⟩
  | cons b w => cases b <;> exact ⟨_, rfl⟩

/-- Zero bits on the right in front of blank tape are blank tape. -/
theorem Rbits_zero_blank (n : Nat) : Rbits (List.replicate n false) blank = blank := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, Rbits, ih]
    show __BLANKZ0__ = blank
    simp only [cons_false_blank]

theorem rotT (a : Nat) (Z : Tape) : rep a [true, true] (cons true Z) = cons true (rep a [true, true] Z) :=
  (rep_rotate a [true] [true, true] [true, true] rfl Z).symm

theorem rotF (j : Nat) (Z : Tape) : rep j Z0 (cons false Z) = cons false (rep j Z0 Z) :=
  (rep_rotate j [false] Z0 Z0 rfl Z).symm

theorem rotTF (a : Nat) (Z : Tape) : cons true (rep a [false, true] Z) = rep a [true, false] (cons true Z) :=
  rep_rotate a [true] [false, true] [true, false] rfl Z

/-! ## One pass pair: minus one on the left, plus one on the right -/

/-- Mode 3 (top block `1^3`): one pass pair takes the left number `0^a 1 w` to `1^a 0 w` and the right number
`1^j 0 v` to `0^j 1 v`, in `4a + 6j + 22` steps (1a, 1b; `__C3__` in general). -/
theorem cyc3 (a j : Nat) (w v : List Bool) (Y X : Tape) :
    steps (__S3__)
      ⟨Lbits (List.replicate a false ++ true :: w) (cons true Y),
        cons false (rep 3 T (Rbits (List.replicate j true ++ false :: v) X)), .A⟩ =
    some ⟨Lbits (List.replicate a true ++ false :: w) (cons true Y),
        cons false (rep 3 T (Rbits (List.replicate j false ++ true :: v) X)), .A⟩ := by
  obtain ⟨Y', hY⟩ := Lbits_head w Y
  have h := pair3 a 0 j Y' (Rbits v X)
  rw [Lbits_zeros, Lbits_ones, Rbits_ones, Rbits_zeros]
  simp only [Lbits, Rbits, hY]
  rw [rotT]
  have e : rep j Z0 (app Z1 (Rbits v X)) = __ROTZ1__ := by
    simp only [app_cons, app_nil, rotF]
  rw [e]
  exact h

/-! ## Binary numbers -/

/-- The `n` low bits of `x`, least significant first. -/
def bitsN : Nat → Nat → List Bool
  | 0, _ => []
  | n + 1, x => (x % 2 == 1) :: bitsN n (x / 2)

/-- Subtracting one: `0^a 1 w` becomes `1^a 0 w`. -/
theorem bits_dec : ∀ (n x : Nat), 1 ≤ x → x < 2 ^ n →
    ∃ a w, bitsN n x = List.replicate a false ++ true :: w ∧ bitsN n (x - 1) = List.replicate a true ++ false :: w := by
  intro n
  induction n with
  | zero => intro x h1 h2; simp at h2; omega
  | succ n ih =>
    intro x h1 h2
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · have h3 : 1 ≤ x / 2 := by omega
      have h4 : x / 2 < 2 ^ n := by rw [Nat.pow_succ] at h2; omega
      obtain ⟨a, w, e1, e2⟩ := ih (x / 2) h3 h4
      refine ⟨a + 1, w, ?_, ?_⟩
      · simp only [bitsN, h, e1]; rfl
      · have h5 : (x - 1) % 2 = 1 := by omega
        have h6 : (x - 1) / 2 = x / 2 - 1 := by omega
        simp only [bitsN, h5, h6, e2]; rfl
    · refine ⟨0, bitsN n (x / 2), ?_, ?_⟩
      · simp only [bitsN, h]; rfl
      · have h5 : (x - 1) % 2 = 0 := by omega
        have h6 : (x - 1) / 2 = x / 2 := by omega
        simp only [bitsN, h5, h6]; rfl

/-- Adding one: `1^j 0 v` becomes `0^j 1 v`. -/
theorem bits_inc : ∀ (n x : Nat), x + 1 < 2 ^ n →
    ∃ j v, bitsN n x = List.replicate j true ++ false :: v ∧ bitsN n (x + 1) = List.replicate j false ++ true :: v := by
  intro n
  induction n with
  | zero => intro x h; simp at h
  | succ n ih =>
    intro x h
    rcases Nat.mod_two_eq_zero_or_one x with h0 | h0
    · refine ⟨0, bitsN n (x / 2), ?_, ?_⟩
      · simp only [bitsN, h0]; rfl
      · have h5 : (x + 1) % 2 = 1 := by omega
        have h6 : (x + 1) / 2 = x / 2 := by omega
        simp only [bitsN, h5, h6]; rfl
    · have h4 : x / 2 + 1 < 2 ^ n := by rw [Nat.pow_succ] at h; omega
      obtain ⟨j, v, e1, e2⟩ := ih (x / 2) h4
      refine ⟨j + 1, v, ?_, ?_⟩
      · simp only [bitsN, h0, e1]; rfl
      · have h5 : (x + 1) % 2 = 0 := by omega
        have h6 : (x + 1) / 2 = x / 2 + 1 := by omega
        simp only [bitsN, h5, h6, e2]; rfl

/-- The configuration of mode 3: the left number `E` in `p` bits above the floor `Y` (which starts with a 1), the
top block `1^3`, the right number `N` in `n` bits below `X`. -/
def C3 (p n E N : Nat) (Y X : Tape) : Config :=
  ⟨Lbits (bitsN p E) (cons true Y), cons false (rep 3 T (Rbits (bitsN n N) X)), .A⟩

/-- Mode 5, first pair: `1^5` on top; the left number loses its lowest 1 bit block `0^a 1` into the top block
`1^(2a+7)`, the right number gains one. -/
def M5 (a : Nat) (w : List Bool) (Y R : Tape) : Config :=
  ⟨Lbits w (cons true Y), cons false (rep a [true, true] (rep 7 T R)), .A⟩

theorem cyc5a (a j : Nat) (w v : List Bool) (Y X : Tape) :
    steps (__S5__)
      ⟨Lbits (List.replicate a false ++ true :: w) (cons true Y),
        cons false (rep 5 T (Rbits (List.replicate j true ++ false :: v) X)), .A⟩ =
    some (M5 a w Y (Rbits (List.replicate j false ++ true :: v) X)) := by
  have h := pair5a a j (Lbits w (cons true Y)) (Rbits v X)
  rw [Lbits_zeros, Rbits_ones, Rbits_zeros]
  simp only [Lbits, Rbits, M5]
  have e : rep j Z0 (app Z1 (Rbits v X)) = __ROTZ1__ := by
    simp only [app_cons, app_nil, rotF]
  rw [e]
  have e7 : ∀ Z : Tape, rep a [true, true] (rep 7 T Z) =
      cons true (cons true (rep a [true, true] (rep 5 T Z))) := by
    intro Z
    rw [show rep 7 T Z = cons true (cons true (rep 5 T Z)) from rfl, rotT, rotT]
  rw [e7]
  exact h

theorem cyc5b (a j : Nat) (w v : List Bool) (Y X : Tape) :
    steps (__S5__) (M5 a w Y (Rbits (List.replicate j true ++ false :: v) X)) =
    some ⟨Lbits (List.replicate a true ++ false :: w) (cons true Y),
        cons false (rep 5 T (Rbits (List.replicate j false ++ true :: v) X)), .A⟩ := by
  obtain ⟨Y', hY⟩ := Lbits_head w Y
  have h := pair5b a 0 j Y' (Rbits v X)
  rw [Lbits_ones, Rbits_ones, Rbits_zeros]
  simp only [M5, Lbits, Rbits, hY]
  have e : rep j Z0 (app Z1 (Rbits v X)) = __ROTZ1__ := by
    simp only [app_cons, app_nil, rotF]
  rw [e, ← rotTF]
  exact h

/-! ## Whole countdowns -/

/-- `c'` is reachable from `c`. -/
def Reach (c c' : Config) : Prop := ∃ n, steps n c = some c'

theorem reach_trans {a b c : Config} : Reach a b → Reach b c → Reach a c
  | ⟨n, h⟩, ⟨m, h'⟩ => ⟨n + m, steps_seq trans h h'⟩

/-- `c'` is reachable from `c` in at least `m` steps (so no halt in the first `m` steps from `c`). -/
def ReachGE (c c' : Config) (m : Nat) : Prop := ∃ n, m ≤ n ∧ steps n c = some c'

theorem reachGE_trans {a b c : Config} {m m' : Nat} : ReachGE a b m → ReachGE b c m' → ReachGE a c (m + m')
  | ⟨n, hn, h⟩, ⟨n', hn', h'⟩ => ⟨n + n', by omega, steps_seq trans h h'⟩

theorem reach_of_ge {a b : Config} {m : Nat} : ReachGE a b m → Reach a b
  | ⟨n, _, h⟩ => ⟨n, h⟩

/-- **Mode-3 countdown.** From `C3 p n E N`, for every `k ≤ E` with `N + k < 2^n`, the machine reaches
`C3 p n (E - k) (N + k)`, in at least __B3__·k steps: k pass pairs, each subtracting one on the left and adding one on the right. -/
theorem run3 (p n : Nat) (Y X : Tape) : ∀ (k E N : Nat), k ≤ E → E < 2 ^ p → N + k < 2 ^ n →
    ReachGE (C3 p n E N Y X) (C3 p n (E - k) (N + k) Y X) (__B3__ * k) := by
  intro k
  induction k with
  | zero => intro E N _ _ _; exact ⟨0, by omega, rfl⟩
  | succ k ih =>
    intro E N h1 h2 h3
    obtain ⟨a, w, e1, e2⟩ := bits_dec p E (by omega) h2
    obtain ⟨j, v, f1, f2⟩ := bits_inc n N (by omega)
    have step1 : ReachGE (C3 p n E N Y X) (C3 p n (E - 1) (N + 1) Y X) __B3__ := by
      refine ⟨__S3__, by omega, ?_⟩
      unfold C3
      rw [e1, e2, f1, f2]
      exact cyc3 a j w v Y X
    have := ih (E - 1) (N + 1) (by omega) (by omega) (by omega)
    rw [show E - 1 - k = E - (k + 1) by omega, show N + 1 + k = N + (k + 1) by omega] at this
    have r := reachGE_trans step1 this
    rw [show __B3__ + __B3__ * k = __B3__ * (k + 1) by omega] at r
    exact r

/-- The configuration of mode 5 (top block `1^5`). -/
def C5 (p n E N : Nat) (Y X : Tape) : Config :=
  ⟨Lbits (bitsN p E) (cons true Y), cons false (rep 5 T (Rbits (bitsN n N) X)), .A⟩

/-- **Mode-5 countdown.** From `C5 p n E N`, for every `k ≤ E` with `N + 2k < 2^n`, the machine reaches
`C5 p n (E - k) (N + 2k)`, in at least __B5__·k steps: k cycles of two pass pairs, each cycle subtracting one on the left and adding two on the
right. -/
theorem run5 (p n : Nat) (Y X : Tape) : ∀ (k E N : Nat), k ≤ E → E < 2 ^ p → N + 2 * k < 2 ^ n →
    ReachGE (C5 p n E N Y X) (C5 p n (E - k) (N + 2 * k) Y X) (__B5__ * k) := by
  intro k
  induction k with
  | zero => intro E N _ _ _; exact ⟨0, by omega, rfl⟩
  | succ k ih =>
    intro E N h1 h2 h3
    obtain ⟨a, w, e1, e2⟩ := bits_dec p E (by omega) h2
    obtain ⟨j, v, f1, f2⟩ := bits_inc n N (by omega)
    obtain ⟨j', v', g1, g2⟩ := bits_inc n (N + 1) (by omega)
    have step1 : ReachGE (C5 p n E N Y X) (C5 p n (E - 1) (N + 2) Y X) __B5__ := by
      have s1 := cyc5a a j w v Y X
      rw [← f2, g1] at s1
      have s2 := cyc5b a j' w v' Y X
      rw [← g2, ← e2, show N + 1 + 1 = N + 2 by omega] at s2
      rw [← f1, ← e1] at s1
      exact ⟨_, by omega, steps_seq trans s1 s2⟩
    have := ih (E - 1) (N + 2) (by omega) (by omega) (by omega)
    rw [show E - 1 - k = E - (k + 1) by omega, show N + 2 + 2 * k = N + 2 * (k + 1) by omega] at this
    have r := reachGE_trans step1 this
    rw [show __B5__ + __B5__ * k = __B5__ * (k + 1) by omega] at r
    exact r

end __NS__
'''


def main():
    M, ns = sys.argv[1], sys.argv[2]
    P = 3 if M.split("_")[4].startswith("1RB") else 5
    out = ["import Machine", "", "/-! Counters of the 1RB1LA_1LC1RD_1LA0LC_1RE0RB_ family, generated by `py/gen_counter.py` of "
           "holdouts/1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB--- (pair rules by `tools/py/bbtools/symtm.py`); do not edit by hand. -/",
           "", f"namespace {ns}", "", "open TM", ""]
    steps = {}
    for name, start, end, doc in pair_rules(M, P):
        t, fin = prove(M, name, start, end, doc=doc)
        steps[name] = fin.steps.lean()
        out.append(t)
        out.append("")
    z0 = "[" + ", ".join(["false"] * P) + "]"
    z1 = "[" + ", ".join(["false"] * (P - 1) + ["true"]) + "]"
    rot = "cons false (rep j Z0 (" + "".join(["cons false ("] * (P - 2)) + "cons true (Rbits v X)" + ")" * (P - 2) + "))"
    blank = "".join(["cons false ("] * P) + "blank" + ")" * P
    body = TEMPLATE.replace("__Z0__", z0).replace("__Z1__", z1).replace("__ROTZ1__", rot).replace("__NS__", ns)
    body = body.replace("__S3__", steps["pair3"]).replace("__S5__", steps["pair5a"]).replace("__C3__", steps["pair3"])
    body = body.replace("__BLANKZ0__", blank)
    b3 = int(steps["pair3"].split("+")[-1]); b5 = 2 * int(steps["pair5a"].split("+")[-1])
    body = body.replace("__B3__", str(b3)).replace("__B5__", str(b5))
    assert steps["pair5a"] == steps["pair5b"], steps
    print("\n".join(out) + body, end="")


if __name__ == "__main__":
    main()
