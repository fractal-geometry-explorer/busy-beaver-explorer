import Family
import TM.RLE

/-!
# 1RB0LC_0RC0RE_1RD1LF_1LE0RA_0LA0LE_0RB---: a long run without a halt, by the run-length simulator and the visit rule

The run-length simulator of `tools/lean/TM/RLE.lean`, with one jump: whenever the head is in A on the 0 in front
of a list of plain blocks `l` that is `big` (the closed-form condition of `Family.lean`), the whole visit is done
at once by `FA.visit_closed`.  Its step count is replaced by the lower bound `lbV l = 5^(k-1)·(5·b_k + 9)` (k
blocks, b_k the last), proved here from the recursion `goT` (`goT_ge`).  Everything else (the unclean visits, the
left end, the F-events) is simulated by runs and crossings.

`bound_of_run`: a run of the simulator that reaches N steps proves that the first N steps from blank tape make no
halt.  `bound_1e30` is one such run, evaluated by `native_decide`.
-/

namespace H123261
namespace FA

open TM

/-! ## A lower bound for the steps of a visit -/

def lastD : List Nat → Nat
  | [] => 0
  | [b] => b
  | _ :: c :: r => lastD (c :: r)

theorem bump_length (d : Nat) (l : List Nat) : (bump d l).length = l.length := by
  cases l <;> rfl

theorem lastD_bump (d : Nat) (l : List Nat) : lastD l ≤ lastD (bump d l) := by
  match l with
  | [] => exact Nat.le_refl _
  | [b] => show b ≤ b + d; omega
  | _ :: c :: r => exact Nat.le_refl _

theorem go_length : ∀ n l, (go n l).length = l.length := by
  intro n
  induction n with
  | zero => intro l; match l with
    | [] => rfl
    | [b] => rfl
    | _ :: _ :: _ => rfl
  | succ n ih => intro l; match l with
    | [] => rfl
    | [b] => rfl
    | b :: c :: bs =>
      simp only [go, List.length_cons, ih, bump_length]

theorem lastD_cons (x : Nat) (X : List Nat) (h : X ≠ []) : lastD (x :: X) = lastD X := by
  match X, h with
  | c :: r, _ => rfl

theorem go_last : ∀ n l, lastD l ≤ lastD (go n l) := by
  intro n
  induction n with
  | zero => intro l; match l with
    | [] => exact Nat.le_refl _
    | [b] => show b ≤ b + 1; omega
    | _ :: _ :: _ => exact Nat.le_refl _
  | succ n ih => intro l; match l with
    | [] => exact Nat.le_refl _
    | [b] => show b ≤ b + 1; omega
    | b :: c :: bs =>
      simp only [go]
      have hne : go n (bump 1 (go n (bump 1 (go n (bump 1 (go n (bump 3 (go n ((c + 1) :: bs))))))))) ≠ [] := by
        intro h
        have := congrArg List.length h
        simp [go_length, bump_length] at this
      rw [lastD_cons _ _ hne]
      have a0 : lastD (b :: c :: bs) ≤ lastD ((c + 1) :: bs) := by
        show lastD (c :: bs) ≤ lastD ((c + 1) :: bs)
        cases bs with
        | nil => show c ≤ c + 1; omega
        | cons _ _ => exact Nat.le_refl _
      have := ih ((c + 1) :: bs)
      have := lastD_bump 3 (go n ((c + 1) :: bs))
      have := ih (bump 3 (go n ((c + 1) :: bs)))
      have := lastD_bump 1 (go n (bump 3 (go n ((c + 1) :: bs))))
      have := ih (bump 1 (go n (bump 3 (go n ((c + 1) :: bs)))))
      have := lastD_bump 1 (go n (bump 1 (go n (bump 3 (go n ((c + 1) :: bs))))))
      have := ih (bump 1 (go n (bump 1 (go n (bump 3 (go n ((c + 1) :: bs)))))))
      have := lastD_bump 1 (go n (bump 1 (go n (bump 1 (go n (bump 3 (go n ((c + 1) :: bs))))))))
      have := ih (bump 1 (go n (bump 1 (go n (bump 1 (go n (bump 3 (go n ((c + 1) :: bs)))))))))
      omega

/-- The lower bound: `5^(k-1)·(5·b_k + 9)` for k blocks, the last `b_k`. -/
def lbV (l : List Nat) : Nat := 5 ^ (l.length - 1) * (5 * lastD l + 9)

theorem goT_ge : ∀ n l, l ≠ [] → l.length ≤ n + 1 → lbV l ≤ goT n l := by
  intro n
  induction n with
  | zero => intro l hne hl; match l with
    | [b] => simp [lbV, lastD, goT]
    | _ :: _ :: _ => simp at hl
  | succ n ih => intro l hne hl; match l with
    | [b] => simp [lbV, lastD, goT]
    | b :: c :: bs =>
      simp only [lbV] at ih ⊢
      simp only [goT]
      have hlen : ∀ t : List Nat, t.length = bs.length + 1 → t ≠ [] ∧ t.length ≤ n + 1 := by
        intro t ht
        refine ⟨?_, ?_⟩
        · intro h; rw [h] at ht; simp at ht
        · simp at hl; omega
      have L0 : ((c + 1) :: bs).length = bs.length + 1 := rfl
      have L1 : (bump 3 (go n ((c + 1) :: bs))).length = bs.length + 1 := by simp [bump_length, go_length]
      have L2 : (bump 1 (go n (bump 3 (go n ((c + 1) :: bs))))).length = bs.length + 1 := by
        simp [bump_length, go_length]
      have L3 : (bump 1 (go n (bump 1 (go n (bump 3 (go n ((c + 1) :: bs))))))).length = bs.length + 1 := by
        simp [bump_length, go_length]
      have L4 : (bump 1 (go n (bump 1 (go n (bump 1 (go n (bump 3 (go n ((c + 1) :: bs))))))))).length =
          bs.length + 1 := by simp [bump_length, go_length]
      -- last blocks
      have a0 : lastD (b :: c :: bs) ≤ lastD ((c + 1) :: bs) := by
        show lastD (c :: bs) ≤ lastD ((c + 1) :: bs)
        cases bs with
        | nil => show c ≤ c + 1; omega
        | cons _ _ => exact Nat.le_refl _
      have a1 : lastD ((c + 1) :: bs) ≤ lastD (bump 3 (go n ((c + 1) :: bs))) :=
        Nat.le_trans (go_last n _) (lastD_bump 3 _)
      have a2 : lastD (bump 3 (go n ((c + 1) :: bs))) ≤ lastD (bump 1 (go n (bump 3 (go n ((c + 1) :: bs))))) :=
        Nat.le_trans (go_last n _) (lastD_bump 1 _)
      have a3 : lastD (bump 1 (go n (bump 3 (go n ((c + 1) :: bs))))) ≤
          lastD (bump 1 (go n (bump 1 (go n (bump 3 (go n ((c + 1) :: bs))))))) :=
        Nat.le_trans (go_last n _) (lastD_bump 1 _)
      have a4 : lastD (bump 1 (go n (bump 1 (go n (bump 3 (go n ((c + 1) :: bs))))))) ≤
          lastD (bump 1 (go n (bump 1 (go n (bump 1 (go n (bump 3 (go n ((c + 1) :: bs))))))))) :=
        Nat.le_trans (go_last n _) (lastD_bump 1 _)
      have i0 := ih _ (hlen _ L0).1 (hlen _ L0).2
      have i1 := ih _ (hlen _ L1).1 (hlen _ L1).2
      have i2 := ih _ (hlen _ L2).1 (hlen _ L2).2
      have i3 := ih _ (hlen _ L3).1 (hlen _ L3).2
      have i4 := ih _ (hlen _ L4).1 (hlen _ L4).2
      rw [L0] at i0; rw [L1] at i1; rw [L2] at i2; rw [L3] at i3; rw [L4] at i4
      simp only [Nat.add_sub_cancel] at i0 i1 i2 i3 i4
      have hl : (b :: c :: bs).length - 1 = bs.length + 1 := by simp
      rw [hl, Nat.pow_succ]
      generalize 5 ^ bs.length = P at i0 i1 i2 i3 i4 ⊢
      generalize lastD (b :: c :: bs) = x at a0 ⊢
      have m0 := Nat.mul_le_mul_left P (show 5 * x + 9 ≤ 5 * lastD ((c + 1) :: bs) + 9 by omega)
      have m1 := Nat.mul_le_mul_left P (show 5 * x + 9 ≤ 5 * lastD (bump 3 (go n ((c + 1) :: bs))) + 9 by omega)
      have m2 := Nat.mul_le_mul_left P
        (show 5 * x + 9 ≤ 5 * lastD (bump 1 (go n (bump 3 (go n ((c + 1) :: bs))))) + 9 by omega)
      have m3 := Nat.mul_le_mul_left P
        (show 5 * x + 9 ≤ 5 * lastD (bump 1 (go n (bump 1 (go n (bump 3 (go n ((c + 1) :: bs))))))) + 9 by omega)
      have m4 := Nat.mul_le_mul_left P
        (show 5 * x + 9 ≤
          5 * lastD (bump 1 (go n (bump 1 (go n (bump 1 (go n (bump 3 (go n ((c + 1) :: bs))))))))) + 9 by omega)
      rw [Nat.mul_assoc, Nat.mul_comm 5, ← Nat.mul_assoc]
      have : P * (5 * x + 9) * 5 = P * (5 * x + 9) + P * (5 * x + 9) + P * (5 * x + 9) + P * (5 * x + 9) +
        P * (5 * x + 9) := by omega
      omega

/-! ## Reading a list of plain blocks off the runs -/

/-- `(10)^j` as a word. -/
def pw10 : Nat → List Bool
  | 0 => []
  | j + 1 => true :: false :: pw10 j

theorem app_pw10 (j : Nat) (X : Tape) : app (pw10 j) X = rep j [true, false] X := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show cons true (cons false (app (pw10 j) X)) = _
    rw [ih]
    rfl

theorem rep_pw10 (n j : Nat) (X : Tape) : rep n (pw10 j) X = rep (n * j) [true, false] X := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [rep_succ, ih, app_pw10, ← rep_add]
    congr 1
    rw [Nat.succ_mul, Nat.add_comm]

/-- All cells blank. -/
def allZero : Side → Bool
  | [] => true
  | (w, _) :: s => w.all (· = false) && allZero s

theorem app_zeros (w : List Bool) (h : w.all (· = false) = true) : app w blank = blank := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp at h
    obtain ⟨rfl, h2⟩ := h
    show cons false (app w blank) = blank
    rw [ih (by simpa using h2)]
    exact cons_false_blank

theorem rep_zeros (n : Nat) (w : List Bool) (h : w.all (· = false) = true) : rep n w blank = blank := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep_succ, ih, app_zeros w h]

theorem allZero_spec : ∀ s : Side, allZero s = true → den s = blank
  | [], _ => rfl
  | (w, n) :: s, h => by
    simp [allZero] at h
    simp only [den_cons]
    rw [allZero_spec s (by simpa using h.2)]
    exact rep_zeros n w (by simpa using h.1)

/-- Inside a block that has `k` copies of `10` so far, read the rest of the blocks. -/
def pB : Nat → Nat → Side → Option (List Nat)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | f + 1, k, (w, n) :: s =>
    if n = 0 ∨ w = [] then pB f k s
    else if w = pw10 (w.length / 2) then pB f (k + n * (w.length / 2)) s
    else if w.head? = some false then none
    else if w = [true] ∧ n = 1 then
      if (TM.pop s).1 then
        (if allZero s then some [k] else (pB f 0 s).map (k :: ·))
      else if allZero (TM.pop s).2 then some [k]
      else pB f (k + 1) (TM.pop s).2
    else pushCells w (rcons w (n - 1) s) |> pB f k

theorem pB_spec : ∀ (f k : Nat) (s : Side) (l : List Nat), pB f k s = some l →
    rep k [true, false] (den s) = enc l
  | 0, _, _, _, h => by simp [pB] at h
  | _ + 1, _, [], _, h => by simp [pB] at h
  | f + 1, k, (w, n) :: s, l, h => by
    simp only [pB] at h
    split at h
    · rename_i hz
      rw [← pB_spec f k s l h]
      rcases hz with hz | hz
      · subst hz; rfl
      · subst hz; simp [rep_nil_word]
    split at h
    · rename_i hw
      rw [← pB_spec f _ s l h, den_cons]
      conv => lhs; rw [hw]
      rw [rep_pw10, rep_add]
    split at h
    · cases h
    split at h
    · rename_i hw
      obtain ⟨rfl, rfl⟩ := hw
      have hp := TM.den_pop s
      split at h
      · rename_i h1
        split at h
        · rename_i hz
          simp at h; subst h
          show rep k [true, false] (cons true (den s)) = rep k [true, false] (cons true blank)
          rw [allZero_spec s hz]
        · cases e : pB f 0 s with
          | none => rw [e] at h; cases h
          | some l' =>
            rw [e] at h
            simp at h; subst h
            have := pB_spec f 0 s l' e
            show rep k [true, false] (cons true (den s)) = rep k [true, false] (cons true (enc l'))
            rw [← this]; rfl
      · rename_i h1
        simp at h1
        split at h
        · rename_i hz
          simp at h; subst h
          show rep k [true, false] (cons true (den s)) = rep k [true, false] (cons true blank)
          rw [hp, h1, allZero_spec _ hz, cons_false_blank]
        · rw [← pB_spec f (k + 1) _ l h]
          show rep k [true, false] (cons true (den s)) = _
          rw [hp, h1, ← rep_app_comm]
          rfl
    · rw [← pB_spec f k _ l h, den_pushCells, den_rcons, den_cons]
      congr 1
      rename_i hz _ _ _
      match n, hz with
      | 0, hz => exact absurd (Or.inl rfl) hz
      | n + 1, _ => rw [rep_succ]; rfl

/-- The right part is `0 enc l`: the list `l`. -/
def parseV (s : Side) : Option (List Nat) :=
  if (TM.pop s).1 then none
  else if allZero (TM.pop s).2 then some []
  else pB (4 * s.length + 64) 0 (TM.pop s).2

theorem parseV_spec (s : Side) (l : List Nat) (h : parseV s = some l) : den s = cons false (enc l) := by
  unfold parseV at h
  rw [TM.den_pop s]
  split at h
  · cases h
  · rename_i h1
    simp at h1
    rw [h1]
    split at h
    · rename_i hz; simp at h; subst h; rw [allZero_spec _ hz]; rfl
    · have := pB_spec _ 0 _ l h
      simp only [rep_zero] at this
      rw [this]

/-! ## The closed-form condition, as a fast test -/

def bigTB : Nat → List Nat → Bool
  | _, [] => true
  | _, [x] => x % 2 == 0 && 2 ≤ x
  | p, x :: y :: r => x % 2 == 0 && 2 + p ≤ x && bigTB (5 * p) (y :: r)

theorem bigTB_spec : ∀ (r : List Nat) (i : Nat), bigTB (18 * 5 ^ i) r = true → bigT 1 i r
  | [], _, _ => trivial
  | [x], _, h => by simp [bigTB] at h; exact ⟨by omega, h.2⟩
  | x :: y :: r, i, h => by
    simp [bigTB] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨by omega, by omega, bigTB_spec (y :: r) (i + 1) ?_⟩
    rw [Nat.pow_succ, show 18 * (5 ^ i * 5) = 5 * (18 * 5 ^ i) by
      rw [Nat.mul_comm (5 ^ i) 5, ← Nat.mul_assoc, Nat.mul_comm 18 5, Nat.mul_assoc]]
    exact h3

def bigB : List Nat → Bool
  | [] => false
  | [b] => b % 2 == 1
  | b :: c :: r => b % 2 == 1 && 7 ≤ b && bigTB 18 (c :: r)

theorem bigB_spec (l : List Nat) (h : bigB l = true) : big l := by
  match l with
  | [b] => simp [bigB] at h; exact h
  | b :: c :: r =>
    simp [bigB] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact ⟨h1, h2, bigTB_spec (c :: r) 0 (by simpa using h3)⟩

/-! ## The jump -/

/-- Plain blocks as runs. -/
def encS : List Nat → Side
  | [] => []
  | b :: P => rcons [true, false] b (([true], 1) :: encS P)

theorem den_encS : ∀ l, den (encS l) = enc l
  | [] => rfl
  | b :: P => by simp only [encS, den_rcons, den_cons, den_encS P]; rfl

/-- The visit rule as a jump: in A on `0 enc l` with `l` big, go to `E` on `1 0 enc (cfl l)`. -/
def jumpV (c : RCfg St) : Option (RCfg St × Nat) :=
  match c.st with
  | .A =>
    match parseV c.r with
    | some l => if bigB l then some (⟨c.l, ([true], 1) :: ([false], 1) :: encS (cfl l), .E⟩, lbV l) else none
    | none => none
  | _ => none

theorem jumpV_ok : JumpOK trans jumpV := by
  intro c c' n h
  obtain ⟨L, R, q⟩ := c
  unfold jumpV at h
  simp only at h
  match q, h with
  | .A, h =>
    simp only at h
    cases e : parseV R with
    | none => rw [e] at h; cases h
    | some l =>
      rw [e] at h
      simp only at h
      split at h
      · rename_i hb
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        have hbig := bigB_spec l hb
        have hne : l ≠ [] := by intro h; subst h; exact hbig
        refine ⟨goT l.length l, goT_ge _ _ hne (Nat.le_succ _), ?_⟩
        have := visit_closed l hbig (den L)
        unfold RCfg.toCfg
        simp only [den_cons, rep_one, app_cons, app_nil, den_encS]
        rw [parseV_spec R l e]
        exact this
      · cases h

/-- The words literal cells are folded into: the rotations of `10` and `1000`. -/
def words : List (List Bool) :=
  [[true, false], [false, true], [true, false, false, false], [false, true, false, false],
   [false, false, true, false], [false, false, false, true]]

/-- The simulator from blank tape in frame-A state C. -/
def start : RCfg St := ⟨[], [], .C⟩

end FA

open TM

/-- A bounded run of the frame-A simulator is a bounded run of this machine. -/
theorem bound_of_run {N fuel : Nat} (h : TM.run FA.trans FA.words FA.jumpV N fuel FA.start 0 = true) :
    ∃ c, steps N init = some c := by
  obtain ⟨d, hd⟩ := TM.run_ok FA.trans FA.words FA.jumpV_ok h
  refine ⟨img d, ?_⟩
  rw [← init_img]
  show TM.steps trans N (img ⟨blank, blank, .C⟩) = _
  rw [steps_img]
  exact congrArg (Option.map img) hd

/-- **No halt in the first 10^30 steps** from blank tape (one evaluation by `native_decide`, a few seconds).  The
longer runs are in `BoundBig.lean`, checked with compiled code by `check_big.sh`. -/
theorem bound_1e30 : ∃ c, steps (10 ^ 30) init = some c :=
  bound_of_run (fuel := 10 ^ 12) (by native_decide)

end H123261
