import Rules
set_option linter.unusedSimpArgs false

/-!
# 1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_0LA---: one sweep over any list of done blocks

At the left end, in state A on a 1, the tape is

    cfg N ds W  =  A>1 (10)^N sep [done blocks ds] W        sep = 0 1 1 0 0  (the separator `. ! 10 .`)

where a done block of value `w` is `(10)^w sep` and `W` is the rest of the tape (the *window*, where the sweep does its
work).  One sweep:

* `rpass`: leaving the left end, the head runs right in state B over every done block (`rb`: `(10)^w sep` is left as
  `(01)^(w-1) 1010101`);
* at the window it applies one local rule and turns back in state A (`w_pair_dot`, `w_pair_bang`, `w_append`);
* `lpass`: coming back, every block is put back, shifted two cells to the left (`lb`: `lbA`, `lbD`, `lb3A`, `lb3D`,
  `lb2A`, `lb2D`; a 2-block is left in state D, which the next block absorbs);
* at the left end the fuel `N` has lost 2 (`endA_s`, `endD_s`, `endA_2`, `endD_2`, `endA_0`, `endD_0`).

`sweep_gen`, `sweep_gen2`, `sweep_gen0` compose these for any window rule; `pair_dot`, `pair_bang`, `append` are the
three commonest rules of the macro machine (`py/mac14.py`), for every list of done blocks of values `≥ 2`.
`own_dot`, `own_bang` are the pair rule when the window is the fuel block itself.  Everything is checked by Lean's
kernel.
-/

namespace H122192

open TM

/-- The separator `0 1 1 0 0`. -/
def sep (s : Tape) : Tape := cons false (cons true (cons true (cons false (cons false s))))

/-- A done block: `(10)^w` and its separator. -/
def blk (w : Nat) (s : Tape) : Tape := rep w [true, false] (sep s)

/-- Done blocks, the one nearest the window first. -/
def blks : List Nat → Tape → Tape
  | [], X => X
  | w :: ds, X => blks ds (blk w X)

/-- The configuration at the left end. -/
def cfg (N : Nat) (ds : List Nat) (W : Tape) : Config :=
  ⟨blank, cons true (rep N [true, false] (sep (blks ds W))), .A⟩

/-- A done block `v + 1` as the right pass leaves it (`(01)^v 101010`, nearest first), less its last cell `1`. -/
def lwm : Nat → Tape → Tape
  | 0, s => s
  | v + 1, s => cons false (cons true (cons false (cons true (cons false (cons true (rep v [true, false] s))))))

/-- The left stream once the right pass has crossed the blocks `ds` (nearest first), from the left part `cons true m`;
`tL ds m = cons true (tLm ds m)`. -/
def tLm : List Nat → Tape → Tape
  | [], m => m
  | w :: ds, m => lwm w (cons true (tLm ds m))

/-- The two ways a put-back stretch of tape can begin: `101010` (head in state A) or `101001` (state D). -/
def preA (s : Tape) : Tape := cons true (cons false (cons true (cons false (cons true (cons false s)))))
def preD (s : Tape) : Tape := cons true (cons false (cons true (cons false (cons false (cons true s)))))

def pre : St → Tape → Tape
  | .D, s => preD s
  | _, s => preA s

/-- Steps to cross a block going right, and coming back. -/
def rbc : Nat → Nat
  | 0 => 0
  | v + 1 => 2 * v + 23

def lbc : Nat → Nat
  | 2 => 9
  | 3 => 11
  | v + 4 => 2 * v + 13
  | _ => 0

def rcost : List Nat → Nat
  | [] => 0
  | w :: ds => rcost ds + rbc w

def lcost : List Nat → Nat
  | [] => 0
  | w :: ds => lbc w + lcost ds

/-- The right pass. -/
theorem rpass (m : Tape) : ∀ (ds : List Nat), (∀ w ∈ ds, 1 ≤ w) → ∀ X : Tape,
    steps (rcost ds) ⟨cons true m, blks ds X, .B⟩ = some ⟨cons true (tLm ds m), X, .B⟩
  | [], _, X => rfl
  | w :: ds, h, X => by
    have h1 := rpass m ds (fun u hu => h u (List.mem_cons_of_mem _ hu)) (blk w X)
    obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by have := h w List.mem_cons_self; omega⟩
    have h2 := rb v (cons true (tLm ds m)) X
    exact steps_seq trans h1 h2

/-- Coming back over one block. -/
theorem lb (w : Nat) (hw : 2 ≤ w) (t Y : Tape) (q : St) (hq : q = .A ∨ q = .D) :
    ∃ q' Y', (q' = .A ∨ q' = .D) ∧ blk w (pre q Y) = pre q' Y' ∧
      steps (lbc w) ⟨lwm w (cons true t), cons true Y, q⟩ = some ⟨t, cons true Y', q'⟩ := by
  match w, hw with
  | 2, _ =>
    rcases hq with rfl | rfl
    · exact ⟨.D, _, Or.inr rfl, rfl, lb2A t Y⟩
    · exact ⟨.D, _, Or.inr rfl, rfl, lb2D t Y⟩
  | 3, _ =>
    rcases hq with rfl | rfl
    · exact ⟨.A, _, Or.inl rfl, rfl, lb3A t Y⟩
    · exact ⟨.A, _, Or.inl rfl, rfl, lb3D t Y⟩
  | v + 4, _ =>
    rcases hq with rfl | rfl
    · exact ⟨.A, _, Or.inl rfl, rfl, lbA v t Y⟩
    · exact ⟨.A, _, Or.inl rfl, rfl, lbD v t Y⟩

/-- The left pass. -/
theorem lpass (m : Tape) : ∀ (ds : List Nat), (∀ w ∈ ds, 2 ≤ w) → ∀ (Y : Tape) (q : St), (q = .A ∨ q = .D) →
    ∃ q' Y', (q' = .A ∨ q' = .D) ∧ blks ds (pre q Y) = pre q' Y' ∧
      steps (lcost ds) ⟨tLm ds m, cons true Y, q⟩ = some ⟨m, cons true Y', q'⟩
  | [], _, Y, q, hq => ⟨q, Y, hq, rfl, rfl⟩
  | w :: ds, h, Y, q, hq => by
    obtain ⟨q1, Y1, hq1, e1, h1⟩ := lb w (h w List.mem_cons_self) (tLm ds m) Y q hq
    obtain ⟨q2, Y2, hq2, e2, h2⟩ := lpass m ds (fun u hu => h u (List.mem_cons_of_mem _ hu)) Y1 q1 hq1
    refine ⟨q2, Y2, hq2, ?_, steps_seq trans h1 h2⟩
    show blks ds (blk w (pre q Y)) = _
    rw [e1, e2]

theorem all_one {ds : List Nat} (h : ∀ w ∈ ds, 2 ≤ w) : ∀ w ∈ ds, 1 ≤ w := fun w hw => by
  have := h w hw; omega

/-- The left part after `start_s` for fuel `n + 3`, less its first cell. -/
def mS (n : Nat) : Tape :=
  cons false (cons true (cons false (cons true (cons false (cons true (cons true
    (rep (n + 2) [false, true] (cons false (cons true blank)))))))))

/-- One sweep with fuel `n + 3 ≥ 3`, for any window rule `hw` that turns back in state A. -/
theorem sweep_gen (n : Nat) (ds : List Nat) (hds : ∀ w ∈ ds, 2 ≤ w) (W Y : Tape) (c : Nat)
    (hw : ∀ L : Tape, steps c ⟨cons true L, W, .B⟩ = some ⟨L, cons true Y, .A⟩) :
    ∃ k, steps k (cfg (n + 3) ds W) = some (cfg (n + 1) ds (preA Y)) := by
  have h0 := start_s (n + 2) (blks ds W)
  have h1 := rpass (mS n) ds (all_one hds) W
  have h2 := hw (tLm ds (mS n))
  obtain ⟨q, Y', hq, e, h3⟩ := lpass (mS n) ds hds Y .A (Or.inl rfl)
  suffices hf : ∃ c4, steps c4 ⟨_, cons true Y', q⟩ = some _ by
    obtain ⟨c4, h4⟩ := hf
    exact ⟨_, steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4)))⟩
  simp only [cfg]
  show ∃ c4, steps c4 ⟨mS n, cons true Y', q⟩ = some ⟨blank, cons true (rep (n + 1) [true, false] (sep (blks ds (pre .A Y)))), .A⟩
  rw [e]
  rcases hq with rfl | rfl
  · exact ⟨_, endA_s n Y'⟩
  · exact ⟨_, endD_s n Y'⟩

/-- The left part after `start_s` for fuel 2, and after `start_z` for fuel 0, less the first cell. -/
def m2 : Tape := cons false (cons true (cons false (cons true (cons false (cons true (cons true
    (cons false (cons true (cons false (cons true blank))))))))))
def m0 : Tape := cons false (cons true (cons false (cons true (cons false (cons true (cons true blank))))))

/-- One sweep with fuel 2. -/
theorem sweep_gen2 (ds : List Nat) (hds : ∀ w ∈ ds, 2 ≤ w) (W Y : Tape) (c : Nat)
    (hw : ∀ L : Tape, steps c ⟨cons true L, W, .B⟩ = some ⟨L, cons true Y, .A⟩) :
    ∃ k, steps k (cfg 2 ds W) = some (cfg 0 ds (preA Y)) := by
  have h0 := start_s 1 (blks ds W)
  have h1 := rpass m2 ds (all_one hds) W
  have h2 := hw (tLm ds m2)
  obtain ⟨q, Y', hq, e, h3⟩ := lpass m2 ds hds Y .A (Or.inl rfl)
  suffices hf : ∃ c4, steps c4 ⟨_, cons true Y', q⟩ = some _ by
    obtain ⟨c4, h4⟩ := hf
    exact ⟨_, steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4)))⟩
  simp only [cfg]
  show ∃ c4, steps c4 ⟨m2, cons true Y', q⟩ = some ⟨blank, cons true (rep 0 [true, false] (sep (blks ds (pre .A Y)))), .A⟩
  rw [e]
  rcases hq with rfl | rfl
  · exact ⟨_, endA_2 Y'⟩
  · exact ⟨_, endD_2 Y'⟩

/-- One sweep with fuel 0: the fuel is refilled to 2 and the separator after it becomes a single `0`
(the list `0 sep v1 ...` becomes `2 . v1 ...`). -/
theorem sweep_gen0 (ds : List Nat) (hds : ∀ w ∈ ds, 2 ≤ w) (W Y : Tape) (c : Nat)
    (hw : ∀ L : Tape, steps c ⟨cons true L, W, .B⟩ = some ⟨L, cons true Y, .A⟩) :
    ∃ k, steps k (cfg 0 ds W) =
      some ⟨blank, cons true (rep 2 [true, false] (cons false (blks ds (preA Y)))), .A⟩ := by
  have h0 := start_z (blks ds W)
  have h1 := rpass m0 ds (all_one hds) W
  have h2 := hw (tLm ds m0)
  obtain ⟨q, Y', hq, e, h3⟩ := lpass m0 ds hds Y .A (Or.inl rfl)
  suffices hf : ∃ c4, steps c4 ⟨_, cons true Y', q⟩ = some _ by
    obtain ⟨c4, h4⟩ := hf
    exact ⟨_, steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4)))⟩
  show ∃ c4, steps c4 ⟨m0, cons true Y', q⟩ = some ⟨blank, cons true (rep 2 [true, false] (cons false (blks ds (pre .A Y)))), .A⟩
  rw [e]
  rcases hq with rfl | rfl
  · exact ⟨_, endA_0 Y'⟩
  · exact ⟨_, endD_0 Y'⟩

/-! ## The window rules -/

theorem sfxw (n : Nat) (s : Tape) : rep n [true, false] (cons true (cons false s)) = rep (n + 1) [true, false] s :=
  rep_app_comm n [true, false] s

theorem rot10 (n : Nat) (s : Tape) : cons true (rep n [false, true] (cons false s)) = rep (n + 1) [true, false] s := by
  have h := rep_rotate n [true] [false, true] [true, false] rfl (cons false s)
  simp only [app_cons, app_nil] at h
  rw [h, sfxw]

/-- Pair rule, separator `.`: `x . y` becomes `x+4 ! y-1` (here `x+1 . m+2` becomes `x+5 ! m+1`). -/
theorem win_dot (x m : Nat) (R : Tape) :
    preA (cons true (cons false (rep x [true, false] (cons true (cons false (cons true (rep (m + 1) [true, false] R)))))))
      = rep (x + 5) [true, false] (cons true (rep (m + 1) [true, false] R)) := by
  simp only [preA]; rw [sfxw]; rfl

theorem win_bang (x m : Nat) (R : Tape) :
    preA (cons true (rep (x + 1) [false, true] (cons false (cons false (rep (m + 1) [true, false] R)))))
      = rep (x + 5) [true, false] (cons false (rep (m + 1) [true, false] R)) := by
  simp only [preA]; rw [rot10]; rfl

/-- The fuel-block tail `1 ! 0`: `(10) 1`, then blank tape. -/
def tl3 : Tape := cons true (cons false (cons true blank))

theorem win_app (x : Nat) :
    preA (cons true (cons false (rep x [true, false] (sep (blk 2 tl3))))) = blk (x + 4) (blk 2 tl3) := rfl

theorem pair_dot (n x m : Nat) (ds : List Nat) (hds : ∀ w ∈ ds, 2 ≤ w) (R : Tape) :
    ∃ k, steps k (cfg (n + 3) ds (rep (x + 1) [true, false] (cons false (rep (m + 2) [true, false] R)))) =
      some (cfg (n + 1) ds (rep (x + 5) [true, false] (cons true (rep (m + 1) [true, false] R)))) := by
  rw [← win_dot]; exact sweep_gen n ds hds _ _ _ (fun L => w_pair_dot m x L R)

theorem pair_bang (n x m : Nat) (ds : List Nat) (hds : ∀ w ∈ ds, 2 ≤ w) (R : Tape) :
    ∃ k, steps k (cfg (n + 3) ds (rep (x + 1) [true, false] (cons true (rep (m + 2) [true, false] R)))) =
      some (cfg (n + 1) ds (rep (x + 5) [true, false] (cons false (rep (m + 1) [true, false] R)))) := by
  rw [← win_bang]; exact sweep_gen n ds hds _ _ _ (fun L => w_pair_bang m x L R)

/-- Append: the window `x sep 1 ! 0` at the right end becomes `x sep 2 sep 1 ! 0`: two more done blocks. -/
theorem append (n x : Nat) (ds : List Nat) (hds : ∀ w ∈ ds, 2 ≤ w) :
    ∃ k, steps k (cfg (n + 3) ds (blk (x + 4) tl3)) = some (cfg (n + 1) (2 :: (x + 4) :: ds) tl3) := by
  have h := sweep_gen n ds hds (blk (x + 4) tl3) (cons true (cons false (rep x [true, false] (sep (blk 2 tl3))))) _
    (fun L => w_append x L)
  rw [win_app] at h
  exact h

/-! ## The other window rules (with fuel `n + 3`) -/

/-- Equal counts give equal tapes. -/
theorem rep_congr {a b : Nat} (h : a = b) (w : List Bool) (s : Tape) : rep a w s = rep b w s := h ▸ rfl

/-- `x ! 1 .` becomes `x+4 . 0 .`. -/
theorem p1_bd (n x : Nat) (ds : List Nat) (hds : ∀ w ∈ ds, 2 ≤ w) (R : Tape) :
    ∃ k, steps k (cfg (n + 3) ds (rep (x + 1) [true, false] (cons true (cons true (cons false (cons false R)))))) =
      some (cfg (n + 1) ds (rep (x + 5) [true, false] (cons false (cons false R)))) :=
  sweep_gen n ds hds _ _ _ (fun L => w_p1_bd x L R)

/-- `x ! 1 !` becomes `x+4 . 0 !`. -/
theorem p1_bb (n x : Nat) (ds : List Nat) (hds : ∀ w ∈ ds, 2 ≤ w) (R : Tape) :
    ∃ k, steps k (cfg (n + 3) ds (rep (x + 1) [true, false] (cons true (cons true (cons false (cons true R)))))) =
      some (cfg (n + 1) ds (rep (x + 5) [true, false] (cons false (cons true R)))) :=
  sweep_gen n ds hds _ _ _ (fun L => w_p1_bb x L R)

/-- `x . 1 !` becomes `x+4 ! 0 !`. -/
theorem p1_db (n x : Nat) (ds : List Nat) (hds : ∀ w ∈ ds, 2 ≤ w) (R : Tape) :
    ∃ k, steps k (cfg (n + 3) ds (rep (x + 1) [true, false] (cons false (cons true (cons false (cons true R)))))) =
      some (cfg (n + 1) ds (rep (x + 5) [true, false] (cons true (cons true R)))) := by
  obtain ⟨k, h⟩ := sweep_gen n ds hds _ _ _ (fun L => w_p1_db x L R)
  refine ⟨k, h.trans (congrArg (fun t => some (cfg (n + 1) ds t)) ?_)⟩
  simp only [preA]; rw [sfxw]; rfl

/-- `x . 1 . z s` becomes `x+5+z s` (two blocks merge). -/
theorem p1_dd (n x z : Nat) (b : Bool) (ds : List Nat) (hds : ∀ w ∈ ds, 2 ≤ w) (R : Tape) :
    ∃ k, steps k (cfg (n + 3) ds (rep (x + 1) [true, false] (cons false (cons true (cons false (cons false
        (rep z [true, false] (cons b R)))))))) =
      some (cfg (n + 1) ds (rep (x + 6 + z) [true, false] (cons b R))) := by
  cases b
  · obtain ⟨k, h⟩ := sweep_gen n ds hds _ _ _ (fun L => w_p1_dd0 x z L R)
    refine ⟨k, h.trans (congrArg (fun t => some (cfg (n + 1) ds t)) ?_)⟩
    simp only [preA]; rw [sfxw, sfxw, ← rep_add, rep_congr (show x + 6 + z = x + 1 + 1 + z + 4 by omega)]; rfl
  · obtain ⟨k, h⟩ := sweep_gen n ds hds _ _ _ (fun L => w_p1_dd1 x z L R)
    refine ⟨k, h.trans (congrArg (fun t => some (cfg (n + 1) ds t)) ?_)⟩
    simp only [preA]; rw [sfxw, sfxw, ← rep_add, rep_congr (show x + 6 + z = x + 1 + 1 + z + 4 by omega)]; rfl

/-- `x ! 0 ! z .` becomes `x+4+z .`. -/
theorem merge (n x z : Nat) (ds : List Nat) (hds : ∀ w ∈ ds, 2 ≤ w) (R : Tape) :
    ∃ k, steps k (cfg (n + 3) ds (rep (x + 1) [true, false] (cons true (cons true (rep z [true, false] (cons false R)))))) =
      some (cfg (n + 1) ds (rep (x + 5 + z) [true, false] (cons false R))) := by
  obtain ⟨k, h⟩ := sweep_gen n ds hds _ _ _ (fun L => w_merge x z L R)
  refine ⟨k, h.trans (congrArg (fun t => some (cfg (n + 1) ds t)) ?_)⟩
  show rep (x + 5) [true, false] (rep z [true, false] (cons false R)) = _
  rw [← rep_add]

/-- `x . 0 ! 0` at the right end becomes `x+4 ! 0`. -/
theorem end_db (n x : Nat) (ds : List Nat) (hds : ∀ w ∈ ds, 2 ≤ w) :
    ∃ k, steps k (cfg (n + 3) ds (rep (x + 1) [true, false] (cons false (cons true blank)))) =
      some (cfg (n + 1) ds (rep (x + 5) [true, false] (cons true blank))) := by
  obtain ⟨k, h⟩ := sweep_gen n ds hds _ _ _ (fun L => w_end_db x L)
  refine ⟨k, h.trans (congrArg (fun t => some (cfg (n + 1) ds t)) ?_)⟩
  simp only [preA]; rw [sfxw]; rfl

/-- `x . 0 . z s` becomes `x sep 1 ! z s`: `x` is done. -/
theorem next (n x z : Nat) (b : Bool) (ds : List Nat) (hds : ∀ w ∈ ds, 2 ≤ w) (R : Tape) :
    ∃ k, steps k (cfg (n + 3) ds (rep (x + 4) [true, false] (cons false (cons false (rep z [true, false] (cons b R)))))) =
      some (cfg (n + 1) ((x + 4) :: ds) (rep 1 [true, false] (cons true (rep z [true, false] (cons b R))))) := by
  cases b
  · exact sweep_gen n ds hds _ _ _ (fun L => w_next0 x z L R)
  · exact sweep_gen n ds hds _ _ _ (fun L => w_next1 x z L R)

/-- `x ! 0` at the right end becomes `x+1 sep 1 ! 0`. -/
theorem end_b (n x : Nat) (ds : List Nat) (hds : ∀ w ∈ ds, 2 ≤ w) :
    ∃ k, steps k (cfg (n + 3) ds (rep (x + 4) [true, false] (cons true blank))) =
      some (cfg (n + 1) ((x + 5) :: ds) tl3) :=
  sweep_gen n ds hds _ _ _ (fun L => w_end_b x L)

/-- `x . 0 . 0 . 0 ! 1 . R` becomes `x sep 2 ! 1 . R`. -/
theorem restart2 (n x : Nat) (ds : List Nat) (hds : ∀ w ∈ ds, 2 ≤ w) (R : Tape) :
    ∃ k, steps k (cfg (n + 3) ds (rep (x + 4) [true, false] (cons false (cons false (cons false (cons true (cons true
        (cons false (cons false R))))))))) =
      some (cfg (n + 1) ((x + 4) :: ds) (rep 2 [true, false] (cons true (cons true (cons false (cons false R)))))) :=
  sweep_gen n ds hds _ _ _ (fun L => w_restart2 x L R)

/-! ## The pair rule on the fuel block itself -/

/-- `A>1 (10)^x s (10)^(y+2) R`. -/
def own (x : Nat) (s : Bool) (y : Nat) (R : Tape) : Config :=
  ⟨blank, cons true (rep x [true, false] (cons s (rep y [true, false] R))), .A⟩

theorem own_dot (x y : Nat) (R : Tape) :
    steps (4 * x + 18) (own x false (y + 2) R) = some (own (x + 2) true (y + 1) R) := by
  have h := own_pair_dot x y R
  have e : cons true (cons false (cons true (rep x [false, true] (cons false (cons true (rep (y + 1) [true, false] R))))))
      = rep (x + 2) [true, false] (cons true (rep (y + 1) [true, false] R)) := by
    rw [show cons true (rep x [false, true] (cons false (cons true (rep (y + 1) [true, false] R))))
        = rep (x + 1) [true, false] (cons true (rep (y + 1) [true, false] R)) from rot10 x _]
    rfl
  simp only [own]; rw [← e]; exact h

theorem own_bang (x y : Nat) (R : Tape) :
    steps (4 * x + 10) (own x true (y + 2) R) = some (own (x + 2) false (y + 1) R) := by
  have h := own_pair_bang x y R
  have e : cons true (cons false (cons true (rep x [false, true] (cons false (cons false (rep (y + 1) [true, false] R))))))
      = rep (x + 2) [true, false] (cons false (rep (y + 1) [true, false] R)) := by
    rw [show cons true (rep x [false, true] (cons false (cons false (rep (y + 1) [true, false] R))))
        = rep (x + 1) [true, false] (cons false (rep (y + 1) [true, false] R)) from rot10 x _]
    rfl
  simp only [own]; rw [← e]; exact h

end H122192
