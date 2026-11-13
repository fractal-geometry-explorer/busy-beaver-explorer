import Macro

/-!
# 1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF: halting is a question about the block machine

* `init_gap`: from blank tape the machine reaches the first gap, `1^3 0 B>0`, after 7 steps.
* `inv_next`: the invariant `Inv` (every block at least one 1, except the one just right of the gap) is kept by
  the macro machine, so it never gets `stuck` (`mrun_ne_stuck`): the rules of `Macro.lean` cover the whole run.
* `halts_iff`: **the machine halts from blank tape if and only if the macro machine reaches `halt`**.
* `mstep_halt_iff`: under the invariant the macro machine halts exactly at `gap 1 [] rs`: an odd block at the left
  end of the tape that has kept a single 1 and has nothing left of it to lean on.
* `wall_chain`, `wall_odd`: at the left end, a block `2^k * q` (q odd) halves k times, each time making a new
  leftmost block; then q = 1 halts and q ≥ 3 starts the next sweep.  So **the machine halts iff some sweep reaches
  the left end of the tape carrying a power of two**.

Everything is checked by Lean's kernel.
-/

namespace H141594

open TM

theorem init_gap : steps 7 init = some (gap 3 [] []) := by
  have h : steps 7 init = some ⟨cons false (rep 3 [true] blank), blank, .B⟩ := rfl
  rw [h]
  simp only [gap, enc, cons_false_blank]

/-- One macro step on any macro configuration. -/
def mnext : MS → MS
  | .gap b ls rs => mstep b ls rs
  | s => s

/-- n macro steps. -/
def mrun : Nat → MS → MS
  | 0, s => s
  | n + 1, s => mrun n (mnext s)

theorem mrun_succ' : ∀ (n : Nat) (s : MS), mrun (n + 1) s = mnext (mrun n s)
  | 0, _ => rfl
  | n + 1, s => by rw [mrun, mrun_succ' n (mnext s)]; rfl

/-- The macro configuration of the run: the first gap. -/
def m0 : MS := .gap 3 [] []

/-- Every block holds at least one 1, except the one just right of the gap, which may be empty. -/
def Inv : MS → Prop
  | .gap b ls rs => 1 ≤ b ∧ (∀ x ∈ ls, 1 ≤ x) ∧ (∀ x ∈ rs.tail, 1 ≤ x)
  | .halt => True
  | .stuck => False

theorem pos_addH {k : Nat} {ls : List Nat} (hk : 1 ≤ k) (h : ∀ x ∈ ls.tail, 1 ≤ x) :
    ∀ x ∈ addH k ls, 1 ≤ x := by
  cases ls with
  | nil => simp [addH, show k ≠ 0 by omega]; omega
  | cons a ls =>
    intro x hx
    simp only [addH, List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · exact h x hx

theorem tail_addH (k : Nat) (ls : List Nat) : ∀ x ∈ (addH k ls).tail, x ∈ ls.tail := by
  cases ls with
  | nil => by_cases hk : k = 0 <;> simp [addH, hk]
  | cons a ls => intro x hx; simpa [addH] using hx

theorem mem_reverseAux {x : Nat} {r t : List Nat} (h : x ∈ r.reverseAux t) : x ∈ r ∨ x ∈ t := by
  rw [List.reverseAux_eq] at h
  simpa using h

theorem tail_sub {ls : List Nat} (h : ∀ x ∈ ls, 1 ≤ x) : ∀ x ∈ ls.tail, 1 ≤ x := by
  cases ls with
  | nil => simp
  | cons a ls => intro x hx; exact h x (List.mem_cons_of_mem _ hx)

theorem inv_next : ∀ s : MS, Inv s → Inv (mnext s)
  | .halt, _ => trivial
  | .stuck, h => h
  | .gap b ls rs, ⟨hb, hl, hr⟩ => by
    show Inv (mstep b ls rs)
    unfold mstep
    rw [if_neg (by omega)]
    split
    · rename_i he
      have hk : 1 ≤ b / 2 := by omega
      split
      · rename_i a l hal
        have hpos := pos_addH hk (tail_sub hl)
        rw [hal] at hpos
        refine ⟨hpos a List.mem_cons_self, fun x hx => hpos x (List.mem_cons_of_mem _ hx), ?_⟩
        exact pos_addH hk hr
      · rename_i hal
        cases ls <;> simp [addH, show b / 2 ≠ 0 by omega] at hal
    · split
      · trivial
      · rename_i t hal
        exfalso
        cases ls with
        | nil =>
          by_cases hk : b / 2 = 0
          · simp [addH, hk] at hal
          · simp [addH, hk] at hal
        | cons a ls =>
          simp only [addH, List.cons.injEq] at hal
          have := hl a List.mem_cons_self
          omega
      · rename_i a l hal
        have hall : ∀ x ∈ addH 3 (addH (b / 2) rs), 1 ≤ x :=
          pos_addH (by omega) (fun x hx => hr x (tail_addH _ _ x hx))
        have hl' : ∀ x ∈ (a + 1) :: l, 1 ≤ x := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · omega
          · exact tail_sub hl x (tail_addH (b / 2) ls x (by rw [hal]; exact hx))
        rw [if_pos (List.all_eq_true.mpr (fun x hx => by simpa using hall x hx))]
        split
        · rename_i n rest hn
          have hm : ∀ x ∈ (addH 3 (addH (b / 2) rs)).reverseAux ((a + 1) :: l), 1 ≤ x := by
            intro x hx
            rcases mem_reverseAux hx with h | h
            · exact hall x h
            · exact hl' x h
          rw [hn] at hm
          exact ⟨hm n List.mem_cons_self, fun x hx => hm x (List.mem_cons_of_mem _ hx), by simp⟩
        · rename_i hn
          cases h : addH 3 (addH (b / 2) rs) with
          | nil => exact absurd h (addH_ne_nil 2 _)
          | cons y r => rw [h] at hn; simp [List.reverseAux] at hn
            -- reverseAux of a nonempty list is nonempty

theorem inv_m0 : Inv m0 := ⟨by omega, by simp, by simp⟩

theorem inv_mrun : ∀ n, Inv (mrun n m0)
  | 0 => inv_m0
  | n + 1 => by rw [mrun_succ']; exact inv_next _ (inv_mrun n)

/-- The rules cover the whole run: the macro machine never gets stuck. -/
theorem mrun_ne_stuck (n : Nat) : mrun n m0 ≠ .stuck := by
  intro h; have := inv_mrun n; rw [h] at this; exact this

theorem mrun_halt : ∀ n s, mrun n .halt = s → s = .halt
  | 0, _, h => h.symm
  | n + 1, s, h => mrun_halt n s h

theorem halts_of_steps {k : Nat} {c c' : Config} (h : steps k c = some c') (h' : Halts trans c') :
    Halts trans c := by
  obtain ⟨n, d, hd, hs⟩ := h'
  exact ⟨k + n, d, steps_seq trans h hd, hs⟩

theorem halts_of_mrun : ∀ (n b : Nat) (ls rs : List Nat), mrun n (.gap b ls rs) = .halt →
    Halts trans (gap b ls rs)
  | 0, _, _, _, h => by cases h
  | n + 1, b, ls, rs, h => by
    simp only [mrun, mnext] at h
    cases hm : mstep b ls rs with
    | gap b' ls' rs' =>
      rw [hm] at h
      exact halts_of_steps (mstep_sound hm) (halts_of_mrun n b' ls' rs' h)
    | halt => exact mstep_halt hm
    | stuck =>
      rw [hm] at h
      have : ∀ k, mrun k .stuck = .stuck := fun k => by induction k <;> simp_all [mrun, mnext]
      rw [this] at h; cases h

theorem mcost_pos (b : Nat) (rs : List Nat) : 1 ≤ mcost b rs := by
  unfold mcost; split <;> omega

theorem reach_mrun (hN : ∀ n, mrun n m0 ≠ .halt) : ∀ n, ∃ t b ls rs, n ≤ t ∧
    steps t init = some (gap b ls rs) ∧ mrun n m0 = .gap b ls rs
  | 0 => ⟨7, 3, [], [], by omega, init_gap, rfl⟩
  | n + 1 => by
    obtain ⟨t, b, ls, rs, hn, ht, hm⟩ := reach_mrun hN n
    have h1 := hN (n + 1)
    have h2 := mrun_ne_stuck (n + 1)
    rw [mrun_succ', hm] at h1 h2 ⊢
    cases hs : mstep b ls rs with
    | gap b' ls' rs' =>
      exact ⟨t + mcost b rs, b', ls', rs', by have := mcost_pos b rs; omega,
        steps_seq trans ht (mstep_sound hs), by simp [mnext, hs]⟩
    | halt => exact absurd (by simp [mnext, hs]) h1
    | stuck => exact absurd (by simp [mnext, hs]) h2

/-- **The reduction.**  The machine halts from blank tape if and only if the macro machine, started at the first
gap, reaches `halt`. -/
theorem halts_iff : HaltsFromBlank ↔ ∃ n, mrun n m0 = .halt := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hN
    have hN' : ∀ n, mrun n m0 ≠ .halt := fun n h => hN ⟨n, h⟩
    refine not_halts_of_forall trans (forall_of_unbounded trans (fun m => ∃ c, steps m init = some c) ?_ ?_) hH
    · intro n
      obtain ⟨t, b, ls, rs, hn, ht, _⟩ := reach_mrun hN' n
      exact ⟨t, hn, _, ht⟩
    · intro m hm; exact hm
  · rintro ⟨n, hn⟩
    exact halts_of_steps init_gap (halts_of_mrun n 3 [] [] hn)

/-- Under the invariant, the macro machine halts exactly at an odd block that kept a single 1 at the left end. -/
theorem mstep_halt_iff {b : Nat} {ls rs : List Nat} (h : Inv (.gap b ls rs)) :
    mstep b ls rs = .halt ↔ b = 1 ∧ ls = [] := by
  obtain ⟨hb, _, _⟩ := h
  constructor
  · intro hm
    unfold mstep at hm
    rw [if_neg (by omega)] at hm
    split at hm
    · split at hm <;> cases hm
    · split at hm
      · rename_i hal
        have h0 : b / 2 = 0 := by
          rcases Nat.eq_zero_or_pos (b / 2) with h0 | h0
          · exact h0
          · exact absurd hal (by rw [show b / 2 = (b / 2 - 1) + 1 by omega]; exact addH_ne_nil _ _)
        rw [h0, addH_zero] at hal
        exact ⟨by omega, hal⟩
      · cases hm
      · split at hm
        · split at hm <;> cases hm
        · cases hm
  · rintro ⟨rfl, rfl⟩; rfl

/-- At the left end of the tape (nothing left of the block), a block `2^(k+1) * q` gives half to a new leftmost
block and the gap moves onto it: `2^k * q`, again at the left end. -/
theorem wall_halve (k q : Nat) (hq : 1 ≤ q) (rs : List Nat) :
    mstep (2 ^ (k + 1) * q) [] rs = .gap (2 ^ k * q) [] (0 :: addH (2 ^ k * q) rs) := by
  have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have e : 2 ^ (k + 1) * q = 2 * (2 ^ k * q) := by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
  have hpos : 1 ≤ 2 ^ k * q := Nat.le_trans hq (Nat.le_mul_of_pos_left q (by omega))
  rw [e]
  unfold mstep
  rw [if_neg (by omega), if_pos (by omega), show 2 * (2 ^ k * q) / 2 = 2 ^ k * q by omega]
  simp [addH, show 2 ^ k * q ≠ 0 by omega]

/-- So a block `2^k * q` arriving at the left end reaches the block `q` at the left end after k macro steps. -/
theorem wall_chain (q : Nat) (hq : 1 ≤ q) : ∀ (k : Nat) (rs : List Nat),
    ∃ rs', mrun k (.gap (2 ^ k * q) [] rs) = .gap q [] rs'
  | 0, rs => ⟨rs, by simp [mrun]⟩
  | k + 1, rs => by
    obtain ⟨rs', h⟩ := wall_chain q hq k (0 :: addH (2 ^ k * q) rs)
    exact ⟨rs', by simp only [mrun, mnext]; rw [wall_halve k q hq rs]; exact h⟩

/-- Then the odd block q at the left end halts if and only if q = 1 (otherwise the gap closes and the next sweep
starts at the right end). -/
theorem wall_odd (q : Nat) (rs : List Nat) (hq : 1 ≤ q) : mstep q [] rs = .halt ↔ q = 1 := by
  constructor
  · intro h
    unfold mstep at h
    rw [if_neg (by omega)] at h
    split at h
    · split at h <;> cases h
    · split at h
      · rename_i hal
        rcases Nat.eq_zero_or_pos (q / 2) with h0 | h0
        · omega
        · exact absurd hal (by rw [show q / 2 = (q / 2 - 1) + 1 by omega]; exact addH_ne_nil _ _)
      · cases h
      · split at h
        · split at h <;> cases h
        · cases h
  · rintro rfl; rfl

end H141594
