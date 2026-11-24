/-! # 1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA: the neighbour invariant Q of the digit model

Abstract digit model (no tape): three neighbouring digits `w y x` (left to right), phases W0..W3 = 0..3, and `r`, the
left run of x (the words `110` between the walls of y and x).  The triple changes only when a carry arrives at x from
below; the rules are those of `sweep_w0`, `sweep_w1`, `sweep_w2` in `lean/Sweeps.lean` and of the chain part of every
sweep: W0 → W1 with its left run 1 shorter, W1 → W2 with its left run 2 shorter, W2 → W3, and W3 → W0 with its left
run 3 longer and a carry into y; y's own steps W1 → W2 and W3 → W0 take 2 from the run on their right (so the run
of x grows by 1 instead of 3), and y's W3 → W0 sends a carry on into w.  Cases where x or y merges are left out.

`Q = r + h(x) + g(y) + 4·phase w mod 16`, with h = (0,1,3,3) and g = (0,0,2,2), does not change (`carry_Q`).  The
run of x is odd exactly when x is W0 (`carry_parity`).  And when a cycle of x ends with x in W0 with run 1 (the only
way a W1 with left run 0 comes out of a cycle), y is W0 or W2 (`merge_left`): of the two merges, `merge_w0_w1` or
`merge_w2_w1`, never a third kind. -/

namespace H153488Q

structure Triple where
  pw : Nat
  py : Nat
  px : Nat
  r  : Nat

def carry (s : Triple) : Option Triple :=
  match s.px with
  | 0 => if s.r = 0 then none else some { s with px := 1, r := s.r - 1 }
  | 1 => if s.r < 2 then none else some { s with px := 2, r := s.r - 2 }
  | 2 => some { s with px := 3 }
  | _ =>
    match s.py with
    | 0 => some { s with px := 0, py := 1, r := s.r + 3 }
    | 1 => some { s with px := 0, py := 2, r := s.r + 1 }
    | 2 => some { s with px := 0, py := 3, r := s.r + 3 }
    | _ => some { s with px := 0, py := 0, r := s.r + 1, pw := (s.pw + 1) % 4 }

def h (p : Nat) : Nat := match p with | 0 => 0 | 1 => 1 | _ => 3
def g (p : Nat) : Nat := match p with | 0 => 0 | 1 => 0 | _ => 2

def Q (s : Triple) : Nat := (s.r + h s.px + g s.py + 4 * s.pw) % 16

def ok (s : Triple) : Prop := s.pw < 4 ∧ s.py < 4 ∧ s.px < 4

theorem carry_Q (s t : Triple) (hs : ok s) (e : carry s = some t) : Q t = Q s ∧ ok t := by
  rcases s with ⟨pw, py, px, r⟩
  rcases hs with ⟨hw, hy, hx⟩
  simp only at hw hy hx
  unfold carry at e
  simp only at e
  match px, hx with
  | 0, _ =>
    by_cases hr : r = 0
    · simp [hr] at e
    · simp [hr] at e; subst e; simp [Q, h, g, ok]; omega
  | 1, _ =>
    by_cases hr : r < 2
    · simp [hr] at e
    · simp [hr] at e; subst e; simp [Q, h, g, ok]; omega
  | 2, _ => simp at e; subst e; simp [Q, h, g, ok]; omega
  | 3, _ =>
    match py, hy with
    | 0, _ => simp at e; subst e; simp [Q, h, g, ok]; omega
    | 1, _ => simp at e; subst e; simp [Q, h, g, ok]; omega
    | 2, _ => simp at e; subst e; simp [Q, h, g, ok]; omega
    | 3, _ => simp at e; subst e; simp [Q, h, g, ok]; omega

theorem carry_parity (s t : Triple) (hs : ok s) (hp : (s.r % 2 = 1) ↔ s.px = 0)
    (e : carry s = some t) : (t.r % 2 = 1) ↔ t.px = 0 := by
  rcases s with ⟨pw, py, px, r⟩
  rcases hs with ⟨hw, hy, hx⟩
  simp only at hw hy hx hp
  unfold carry at e
  simp only at e
  match px, hx with
  | 0, _ =>
    by_cases hr : r = 0
    · simp [hr] at e
    · simp [hr] at e; subst e; simp at hp ⊢; omega
  | 1, _ =>
    by_cases hr : r < 2
    · simp [hr] at e
    · simp [hr] at e; subst e; simp at hp ⊢; omega
  | 2, _ => simp at e; subst e; simp at hp ⊢; omega
  | 3, _ =>
    match py, hy with
    | 0, _ => simp at e; subst e; simp at hp ⊢; omega
    | 1, _ => simp at e; subst e; simp at hp ⊢; omega
    | 2, _ => simp at e; subst e; simp at hp ⊢; omega
    | 3, _ => simp at e; subst e; simp at hp ⊢; omega

/-- A cycle of x that ends in W0 with left run 1 (next carry: W1 with left run 0, the merge case) leaves y in W0
or W2. -/
theorem merge_left (s t : Triple) (hs : ok s) (h3 : s.px = 3) (e : carry s = some t) (h1 : t.r = 1) :
    t.px = 0 ∧ (t.py = 0 ∨ t.py = 2) := by
  rcases s with ⟨pw, py, px, r⟩
  rcases hs with ⟨hw, hy, hx⟩
  simp only at hw hy hx h3
  subst h3
  unfold carry at e
  simp only at e
  match py, hy with
  | 0, _ => simp at e; subst e; simp at h1
  | 1, _ => simp at e; subst e; simp
  | 2, _ => simp at e; subst e; simp at h1
  | 3, _ => simp at e; subst e; simp

end H153488Q
