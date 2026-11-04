import OffsetData
import Finish

/-!
# `pre` never gets stuck

`Offset.lean` describes every configuration that `pre` reaches from a list of blocks of at least 2 by one of the 4,463
descriptions of `OffsetData.lean`.  Here: at every one of them the block machine has a next step, unless `pre` stops
or takes a word from the supply there (`progA`, checked by the kernel on the tree), and at most two words are ever
taken (`a.u ≤ 2`).  With the key of `Finish.lean`, which goes down at every step, this gives: from a list of blocks of
at least 2, `pre` stops as soon as the head stays within `N` cells of the right end (`pre_stops`), and then the next
pass start has blocks of at least 2 and last block `2j + c ≥ 2j - 1` (`recur_next_bounded`).  What is left open is
only that the head does not drift left without bound.
-/

namespace BB6c

/-! ## The concrete step exists -/

theorem bstep_go (n c d : Nat) (M : List Nat) (k : Nat) (W : List Nat) : ∃ c', bstep n c d M k W = some (.go c') := by
  unfold bstep
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- The head count each state needs. -/
def hOk (q : St) (h : Nat) : Prop :=
  match q with
  | .A => True
  | .E => h = 1
  | _ => h = 0

/-- **The block machine has a next step** when there is a word in front, the head count fits the state, and the word
in front is not `0` in the states that need one. -/
theorem astep_go {q : St} {h : Nat} {L : List Nat} {w : Nat} {W : List Nat} (hh : hOk q h)
    (hw : w ≠ 0 ∨ q = .B ∨ q = .F ∨ (q = .A ∧ h ≠ 0) ∨ (q = .C ∧ L.headD 0 ≠ 0)) :
    ∃ c', astep ⟨q, h, L, w :: W⟩ = some (.go c') := by
  obtain ⟨n, c, d, e, M, hP⟩ : ∃ n c d e M, pad 4 L = n :: c :: d :: e :: M := ⟨_, _, _, _, _, rfl⟩
  have hn : L.headD 0 = n := by
    have : (pad 4 L).headD 0 = L.headD 0 := by cases L <;> rfl
    rw [← this, hP]; rfl
  rw [hn] at hw
  unfold astep; simp only [hP]
  cases q <;> simp only [hOk] at hh
  · -- A
    rcases h with _ | h
    · rcases w with _ | w
      · simp at hw
      · rcases n with _ | n <;> exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · -- B
    subst hh
    rcases n with _ | _ | n <;> rcases c with _ | c <;> exact bstep_go _ _ _ _ _ _
  · -- C
    subst hh
    rcases n with _ | n
    · rcases w with _ | _ | w
      · simp at hw
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    · rcases w with _ | _ | w
      · exact ⟨_, rfl⟩
      · rcases W with _ | ⟨k, W⟩
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
  · -- D
    subst hh
    rcases w with _ | _ | _ | w
    · simp at hw
    all_goals exact ⟨_, rfl⟩
  · -- E
    subst hh
    rcases w with _ | _ | _ | w
    · simp at hw
    all_goals exact ⟨_, rfl⟩
  · -- F
    subst hh; exact ⟨_, rfl⟩

/-! ## On the descriptions -/

instance (q : St) (h : Nat) : Decidable (hOk q h) := by cases q <;> unfold hOk <;> infer_instance

/-- The code of the word in front, if there is one. -/
def frontA (a : AC) : Option Nat :=
  match a.wx, a.wr with
  | x :: _, _ => some x
  | [], some (_, s) => some s
  | [], none => none

/-- `pre` takes a word from the supply, or the step exists for every configuration the description covers. -/
def progA (a : AC) : Bool :=
  match frontA a with
  | none => true
  | some w =>
    (a.q == .C && a.wx == [1] && a.wr == none) ||
    (decide (hOk a.q a.h) &&
      (w != 0 || a.q == .B || a.q == .F || (a.q == .A && a.h != 0) ||
        (a.q == .C && match a.lx with | x :: _ => x != 0 | [] => a.lr == 1)))

theorem hOk_of {q : St} {d h : Nat} (hd : gD d h) (e : hOk q d) : hOk q h := by
  cases q <;> simp only [hOk] at e ⊢
  all_goals first | trivial | (subst e; exact gD_small hd (by omega))

theorem progA_sound {a : AC} {u : Nat} {c : ACfg} (hc : gC a u c) (hp : progA a = true) (hne : c.W ≠ [])
    (hC : ¬(c.q = .C ∧ c.W = [1])) : ∃ c', astep c = some (.go c') := by
  obtain ⟨q, h, L, W⟩ := c
  obtain ⟨hu, hq, hh, hL, hW⟩ := hc
  simp only at hq hh hL hW hne hC
  obtain ⟨w, W, rfl⟩ : ∃ w W', W = w :: W' := by cases W with | nil => exact absurd rfl hne | cons w W => exact ⟨w, W, rfl⟩
  obtain ⟨x, hx, hxw⟩ : ∃ x, frontA a = some x ∧ gD x w := by
    unfold frontA
    match hwx : a.wx, hwr : a.wr, hW with
    | x :: _, _, hW => exact ⟨x, rfl, hW.1⟩
    | [], some (e, s), hW =>
      refine ⟨s, rfl, ?_⟩
      cases hW with
      | one h1 h2 => exact .inl ⟨by omega, rfl⟩
      | cons h1 h2 _ _ => exact .inl ⟨by omega, rfl⟩
    | [], none, hW => simp [gW] at hW
  unfold progA at hp
  rw [hx] at hp
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at hp
  rcases hp with ⟨⟨hqC, hx1⟩, hr⟩ | ⟨hok, hw⟩
  · exfalso; apply hC
    refine ⟨by rw [← hq, hqC], ?_⟩
    rw [hx1, hr] at hW
    obtain ⟨h1, h2⟩ := hW
    simp only [gW] at h2
    rw [gD_small h1 (by omega), h2]
  · rw [← hq]
    refine astep_go (hOk_of hh hok) ?_
    rcases hw with ((((hw | hw) | hw) | ⟨hw1, hw2⟩) | ⟨hw1, hw2⟩)
    · exact .inl fun h0 => hw (by subst h0; exact gD_0 hxw)
    · exact .inr (.inl hw)
    · exact .inr (.inr (.inl hw))
    · exact .inr (.inr (.inr (.inl ⟨hw1, fun h0 => hw2 (by subst h0; exact gD_0 hh)⟩)))
    · refine .inr (.inr (.inr (.inr ⟨hw1, ?_⟩)))
      match hlx : a.lx, hL with
      | x :: _, hL =>
        rw [hlx] at hw2; simp at hw2
        exact fun h0 => hw2 (by have := hL.1; rw [h0] at this; exact gD_0 this)
      | [], hL =>
        rw [hlx] at hw2; simp at hw2
        rw [hw2] at hL
        obtain ⟨b, g, z, hLe, hb, -, -⟩ := hL
        rw [hLe]; simp; omega

/-- **Every reachable description has a next step or a supply word, and at most two supply words are taken** (kernel
only). -/
theorem prog_ok : reachT.toList.all (fun a => progA a && decide (a.u ≤ 2)) = true := by decide +kernel

/-! ## `pre` stops when the cells stay bounded -/

/-- The descriptions in the tree hold all along a run of `pre` from a pass start. -/
def Inv (c : ACfg) (u : Nat) : Prop := ∃ a ∈ reachT.toList, gC a u c

/-- The configurations a run of `pre` passes through, from `c₀` with no supply words taken. -/
inductive PreR (c₀ : ACfg) : ACfg → Nat → Prop
  | start : PreR c₀ c₀ 0
  | unf {c : ACfg} {u : Nat} : PreR c₀ c u → ¬(c.q = .A ∧ c.h = 0 ∧ allTwo c.W = true) →
      (c.W = [] ∨ (c.q = .C ∧ c.W = [1])) → PreR c₀ ⟨c.q, c.h, c.L, c.W ++ [2]⟩ (u + 1)
  | step {c c' : ACfg} {u : Nat} : PreR c₀ c u → ¬(c.q = .A ∧ c.h = 0 ∧ allTwo c.W = true) →
      ¬(c.W = [] ∨ (c.q = .C ∧ c.W = [1])) → astep c = some (.go c') → PreR c₀ c' u

theorem preR_inv {ls : List Nat} (hg : ∀ b ∈ ls, 2 ≤ b) {c : ACfg} {u : Nat}
    (h : PreR ⟨.B, 0, pad 1 ls, [0, 1]⟩ c u) : Inv c u := by
  obtain ⟨hs, hT⟩ := checkT_sound check_ok
  induction h with
  | start =>
    obtain ⟨a, ha, -, hc⟩ := start_mem hg
    exact ⟨a, hs a ha, hc⟩
  | unf _ hs1 hs2 ih =>
    obtain ⟨a, ha, hc⟩ := ih
    obtain ⟨o, ho, hg'⟩ := (absNext_sound hc hs1).1 hs2
    obtain ⟨b, rfl, hb, -⟩ := (hT a ha).2 o ho
    exact ⟨b, hb, hg'⟩
  | step _ hs1 hs2 e ih =>
    obtain ⟨a, ha, hc⟩ := ih
    obtain ⟨o, ho, hg'⟩ := (absNext_sound hc hs1).2 _ hs2 e
    obtain ⟨b, rfl, hb, -⟩ := (hT a ha).2 o ho
    exact ⟨b, hb, hg'⟩

theorem inv_prog {c : ACfg} {u : Nat} (h : Inv c u) : u ≤ 2 ∧
    (c.W ≠ [] → ¬(c.q = .C ∧ c.W = [1]) → ∃ c', astep c = some (.go c')) := by
  obtain ⟨a, ha, hc⟩ := h
  have := List.all_eq_true.1 prog_ok a ha
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨hc.1 ▸ this.2, fun hne hC => progA_sound hc this.1 hne hC⟩

theorem pre_stops_of {c₀ : ACfg} {N : Nat} (hI : ∀ c u, PreR c₀ c u → Inv c u)
    (hN : ∀ c u, PreR c₀ c u → (key c).length ≤ N) :
    ∀ (f : Nat) {c : ACfg} {u : Nat}, PreR c₀ c u → (3 - u) * 3 ^ N + val N (key c) < f →
      ∃ r, pre f c u = some r := by
  intro f
  induction f with
  | zero => intro c u _ hf; omega
  | succ f ih =>
    intro c u hr hf
    obtain ⟨hu, hp⟩ := inv_prog (hI c u hr)
    unfold pre
    split
    · exact ⟨_, rfl⟩
    rename_i hs1
    split
    · rename_i hs2
      apply ih (.unf hr hs1 hs2)
      have := val_lt N (key ⟨c.q, c.h, c.L, c.W ++ [2]⟩)
      have : (3 - u) * 3 ^ N = (3 - (u + 1)) * 3 ^ N + 3 ^ N := by
        rw [show 3 - u = (3 - (u + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]
      omega
    · rename_i hs2
      have hne : c.W ≠ [] := fun h => hs2 (.inl h)
      have hC : ¬(c.q = .C ∧ c.W = [1]) := fun h => hs2 (.inr h)
      obtain ⟨c', e⟩ := hp hne hC
      rw [e]
      apply ih (.step hr hs1 hs2 e)
      have := val_mono (astep_key e) (hN c u hr)
      omega

/-- **`pre` stops when the cells stay bounded** (kernel only).  From a pass start with blocks at least 2, if every
configuration of the run has at most `N` cells (head offset plus the cells of the words), `pre` stops within
`4 · 3^N` steps.  The run never gets stuck: every reachable description passes `progA`. -/
theorem pre_stops {ls : List Nat} (hg : ∀ b ∈ ls, 2 ≤ b) {N : Nat}
    (hN : ∀ c u, PreR ⟨.B, 0, pad 1 ls, [0, 1]⟩ c u → (key c).length ≤ N) :
    ∃ r, pre (4 * 3 ^ N) ⟨.B, 0, pad 1 ls, [0, 1]⟩ 0 = some r :=
  pre_stops_of (fun _ _ h => preR_inv hg h) hN _ .start (by have := val_lt N (key ⟨.B, 0, pad 1 ls, [0, 1]⟩); omega)

/-- **The next pass start, with only the bound left** (kernel only).  For every list `ls` of blocks of at least 2
whose run of `pre` keeps at most `N` cells, for every `j ≥ 2` the pass from a last block `3j` reaches a pass start with
all blocks at least 2 and last block `2j + c`, `c ≥ -1`, and `c ≥ 0` unless `ls` starts with 2. -/
theorem recur_next_bounded {ls : List Nat} (hg : ∀ b ∈ ls, 2 ≤ b) {N : Nat}
    (hN : ∀ c u, PreR ⟨.B, 0, pad 1 ls, [0, 1]⟩ c u → (key c).length ≤ N) (j : Nat) (hj : 2 ≤ j) :
    ∃ ls' n, (∀ b ∈ ls', 2 ≤ b) ∧ Reaches (K ls (3 * j - 1)) (K ls' n) ∧
      2 * j ≤ n + 1 + (if ls.headD 0 = 2 then 1 else 0) := by
  obtain ⟨⟨L, p, u⟩, e⟩ := pre_stops hg hN
  exact recur_next hg e j hj

end BB6c
