/-! # 1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---: the neighbour invariant K of the digit model

Abstract digit model (no tape): a pair of neighbouring digits `y x` (y left of x), each with a phase
S0..S3 = 0..3, and `r`, the left run of x (the words `100` between the walls of y and x).  The pair changes only when
a carry arrives at x from below; the rules are those of `sweep_s0`, `sweep_s1`, `sweep_s2` and the chain part of
every sweep in `lean/Sweeps.lean` (S0 → S1; S1 → S2 with its left run one shorter; S2 → S3; S3 → S0 with a carry into
y, whose phase steps by one).  The merge case (x in S1 with left run 0) is left out: there the pair ends.

`K = phase y + r + [phase x ≥ 2] mod 4` does not change while the pair lives (`carry_K`), and when x's run is used
up the left neighbour is in phase K (`merge_phase`), so the kind of merge is fixed when the pair is created. -/

namespace H159355K

structure Pair where
  py : Nat   -- phase of y (0..3)
  px : Nat   -- phase of x (0..3)
  r  : Nat   -- left run of x

/-- A carry arrives at x.  `none` is the merge case (x in S1 with left run 0). -/
def carry (s : Pair) : Option Pair :=
  match s.px with
  | 0 => some { s with px := 1 }
  | 1 => if s.r = 0 then none else some { s with px := 2, r := s.r - 1 }
  | 2 => some { s with px := 3 }
  | _ => some { s with px := 0, py := (s.py + 1) % 4 }

def ind (p : Nat) : Nat := if p ≥ 2 then 1 else 0

def K (s : Pair) : Nat := (s.py + s.r + ind s.px) % 4

theorem carry_K (s t : Pair) (hx : s.px < 4) (h : carry s = some t) : K t = K s := by
  unfold carry at h
  rcases s with ⟨py, px, r⟩
  simp only at hx h
  match px, hx with
  | 0, _ => simp at h; subst h; simp [K, ind]
  | 1, _ =>
    by_cases hr : r = 0
    · simp [hr] at h
    · simp [hr] at h; subst h; simp [K, ind]; omega
  | 2, _ => simp at h; subst h; simp [K, ind]
  | 3, _ => simp at h; subst h; simp [K, ind]; omega

theorem carry_phase (s t : Pair) (hx : s.px < 4) (hy : s.py < 4) (h : carry s = some t) :
    t.px < 4 ∧ t.py < 4 := by
  unfold carry at h
  rcases s with ⟨py, px, r⟩
  simp only at hx hy h
  match px, hx with
  | 0, _ => simp at h; subst h; simp; omega
  | 1, _ =>
    by_cases hr : r = 0
    · simp [hr] at h
    · simp [hr] at h; subst h; simp; omega
  | 2, _ => simp at h; subst h; simp; omega
  | 3, _ => simp at h; subst h; simp; omega

/-- At the merge (x in S1, left run 0) the phase of y is K. -/
theorem merge_phase (s : Pair) (hy : s.py < 4) (h1 : s.px = 1) (h0 : s.r = 0) : s.py = K s := by
  rcases s with ⟨py, px, r⟩
  simp only at hy h1 h0; subst h1; subst h0; simp [K, ind]; omega

/-- K is the same along any number of carries that do not merge. -/
theorem iter_K (n : Nat) : ∀ (s t : Pair), s.px < 4 → s.py < 4 →
    (Nat.repeat (fun o => o.bind carry) n (some s)) = some t → K t = K s := by
  induction n with
  | zero => intro s t _ _ h; simp [Nat.repeat] at h; subst h; rfl
  | succ n ih =>
    intro s t hx hy h
    simp only [Nat.repeat] at h
    cases hm : Nat.repeat (fun o => o.bind carry) n (some s) with
    | none => simp [hm] at h
    | some u =>
      simp [hm] at h
      have hu := ih s u hx hy hm
      have hb : u.px < 4 ∧ u.py < 4 := by
        clear h hu ih
        induction n generalizing u with
        | zero => simp [Nat.repeat] at hm; subst hm; exact ⟨hx, hy⟩
        | succ n ih2 =>
          simp only [Nat.repeat] at hm
          cases hm2 : Nat.repeat (fun o => o.bind carry) n (some s) with
          | none => simp [hm2] at hm
          | some v => simp [hm2] at hm; have := ih2 v hm2; exact carry_phase v u this.1 this.2 hm
      rw [carry_K u t hb.1 h, hu]

end H159355K
