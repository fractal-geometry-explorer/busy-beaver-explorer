import Total

/-! # How many visits a defect needs (machine-independent part of `Fuel.lean`)

Token level only (it imports `Total.lean`, not a machine), so that both this machine and the twin
1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC--- can state their reductions with the same `nx` and `R9`.
See `Fuel.lean` for the explanation; the definitions and proofs here were moved from there unchanged.
-/

namespace F36869

open Z36869

/-! ## The fuel a defect needs -/

mutual
/-- Visits of A after which `x W` is clean. -/
def nx : List T → Nat
  | [] => 1
  | .O :: w => 2 * nx w + 1
  | .L :: w => (nx w + 1) / 2
  | .I :: w => ne w + 1
  | _ :: _ => 0
/-- Visits of A after which the tape `Eh W` leaves is clean. -/
def ne : List T → Nat
  | [] => 0
  | .L :: w => (ne w + 1) / 2
  | .O :: w => 2 * ne w + 1
  | .I :: w => n0 w
  | _ :: _ => 0
/-- Visits of A after which the tape `E0 W` leaves is clean. -/
def n0 : List T → Nat
  | [] => 0
  | .O :: _ => 0
  | .L :: w => 2 * (nx w - 1)
  | .I :: w => 2 * (2 * ne w + 1)
  | _ :: _ => 0
end

/-! ## Clean tapes stay clean -/

theorem clean_step {k w a} (h : TV k w a) : k = .A → Clean w → Clean a := by
  induction h with
  | aL _ _ ih1 ih2 =>
    intro _ hc
    have hb := ih2 rfl (ih1 rfl (clean_tail hc))
    exact clean_cons (Or.inl rfl) hb
  | aO w => intro _ hc; exact clean_cons (Or.inr (Or.inr rfl)) (clean_tail hc)
  | aI _ ih => intro _ hc; exact clean_cons (Or.inr (Or.inl rfl)) (ih rfl (clean_tail hc))
  | aNil => intro _ _; exact clean_cons (Or.inr (Or.inr rfl)) clean_nil
  | az w => intro _ hc; have := clean_head hc; simp at this
  | axO w => intro _ hc; have := clean_head hc; simp at this
  | axI _ _ => intro _ hc; have := clean_head hc; simp at this
  | axL _ _ _ _ => intro _ hc; have := clean_head hc; simp at this
  | a1 _ _ => intro _ hc; have := clean_head hc; simp at this
  | axEnd _ _ => intro _ hc; have := clean_head hc; simp at this
  | hL _ _ => intro h; cases h
  | hO w => intro h; cases h
  | hI _ _ => intro h; cases h
  | hNil => intro h; cases h
  | oO w => intro h; cases h
  | oL _ _ => intro h; cases h
  | oI w => intro h; cases h
  | oNil => intro h; cases h

theorem clean_tvn {n w r} (h : TVn n w r) : Clean w → Clean r := by
  induction h with
  | zero => exact id
  | succ h1 _ ih => exact fun hw => ih (clean_step h1 rfl hw)

theorem clean_I : Clean [T.I] := clean_cons (Or.inr (Or.inr rfl)) clean_nil

theorem clean_dig {d q} (hd : d = T.O ∨ d = T.I) (h : Clean q) : Clean (d :: q) :=
  clean_cons (Or.inr hd) h

/-! ## Visits through a word in front -/

theorem tvn_L : ∀ n {r q}, TVn n (.L :: r) q → ∃ q', q = .L :: q' ∧ TVn (2 * n) r q'
  | 0, r, q, h => ⟨r, TVn.zero_inv h, TVn.zero r⟩
  | n + 1, r, q, h => by
    obtain ⟨a, ha, hq⟩ := TVn.succ_inv h
    cases ha with
    | aL h1 h2 =>
      obtain ⟨q', rfl, hq'⟩ := tvn_L n hq
      refine ⟨q', rfl, ?_⟩
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
      exact TVn.succ h1 (TVn.succ h2 hq')

theorem tvn_dig : ∀ n,
    (∀ {r q}, TVn n (.O :: r) q → ∃ q', TVn (n / 2) r q' ∧ (q = .O :: q' ∨ q = .I :: q')) ∧
    (∀ {r q}, TVn n (.I :: r) q → ∃ q', TVn ((n + 1) / 2) r q' ∧ (q = .O :: q' ∨ q = .I :: q'))
  | 0 => ⟨fun h => ⟨_, TVn.zero _, Or.inl (TVn.zero_inv h)⟩, fun h => ⟨_, TVn.zero _, Or.inr (TVn.zero_inv h)⟩⟩
  | n + 1 => by
    obtain ⟨hO, hI⟩ := tvn_dig n
    constructor
    · intro r q h
      obtain ⟨a, ha, hq⟩ := TVn.succ_inv h
      cases ha with
      | aO _ =>
        obtain ⟨q', h', e⟩ := hI hq
        exact ⟨q', by simpa using h', e⟩
    · intro r q h
      obtain ⟨a, ha, hq⟩ := TVn.succ_inv h
      cases ha with
      | aI h1 =>
        obtain ⟨q', h', e⟩ := hO hq
        refine ⟨q', ?_, e⟩
        rw [show (n + 1 + 1) / 2 = n / 2 + 1 by omega]
        exact TVn.succ h1 h'

theorem tvn_O {n r q} (h : TVn n (.O :: r) q) : ∃ q', TVn (n / 2) r q' ∧ (q = .O :: q' ∨ q = .I :: q') :=
  (tvn_dig n).1 h

theorem clean_of_dig {q q'} (e : q = T.O :: q' ∨ q = T.I :: q') (h : Clean q') : Clean q := by
  rcases e with rfl | rfl
  · exact clean_dig (Or.inl rfl) h
  · exact clean_dig (Or.inr rfl) h

/-! ## The fuel is enough -/

theorem nx_pos : ∀ w, Clean w → 1 ≤ nx w
  | [], _ => by simp [nx]
  | t :: w, h => by
    have hw := nx_pos w (clean_tail h)
    rcases clean_head h with rfl | rfl | rfl <;> simp only [nx] <;> omega

/-- `1 W` from what `Eh W` needs: its first visit is `O Eh(W)`. -/
theorem one_of_eh {W} (H : ∀ e, TV .Eh W e → ∀ n r, ne W ≤ n → TVn n e r → Clean r) :
    ∀ n r, 2 * ne W + 1 ≤ n → TVn n (.one :: W) r → Clean r := by
  intro n r hn h
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨a, ha, hr⟩ := TVn.succ_inv h
  cases ha with
  | a1 he =>
    obtain ⟨q, hq, e⟩ := tvn_O hr
    exact clean_of_dig e (H _ he _ _ (by omega) hq)

/-- The fuel functions are enough, for `x W`, for `Eh W` and for `E0 W`. -/
theorem fuel : ∀ W : List T, Clean W →
    (∀ n r, nx W ≤ n → TVn n (.x :: W) r → Clean r) ∧
    (∀ e, TV .Eh W e → ∀ n r, ne W ≤ n → TVn n e r → Clean r) ∧
    (∀ e, TV .E0 W e → ∀ n r, n0 W ≤ n → TVn n e r → Clean r)
  | [], _ => by
    refine ⟨?_, ?_, ?_⟩
    · intro n r hn h
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp [nx] at hn; omega⟩
      obtain ⟨a, ha, hr⟩ := TVn.succ_inv h
      cases ha with
      | axEnd h1 => exact clean_tvn hr (clean_step h1 rfl clean_I)
    · intro e he n r _ h
      cases he
      exact clean_tvn h clean_I
    · intro e he n r _ h
      cases he
      exact clean_tvn h (clean_cons (Or.inl rfl) clean_nil)
  | t :: w, hc => by
    have hw := clean_tail hc
    obtain ⟨Px, Pe, P0⟩ := fuel w hw
    have P1 := one_of_eh Pe
    rcases clean_head hc with rfl | rfl | rfl
    · -- t = L
      refine ⟨?_, ?_, ?_⟩
      · intro n r hn h
        have hp := nx_pos w hw
        simp only [nx] at hn
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        obtain ⟨a, ha, hr⟩ := TVn.succ_inv h
        cases ha with
        | axL h1 h2 =>
          obtain ⟨q, rfl, hq⟩ := tvn_L n' hr
          have hx : TVn (2 * n' + 1 + 1) (.x :: w) q := TVn.succ h1 (TVn.succ h2 hq)
          exact clean_cons (Or.inl rfl) (Px _ _ (by omega) hx)
      · intro e he n r hn h
        cases he with
        | hL he' =>
          simp only [ne] at hn
          obtain ⟨q, rfl, hq⟩ := tvn_L n h
          exact clean_cons (Or.inl rfl) (Pe _ he' _ _ (by omega) hq)
      · intro e he n r hn h
        cases he with
        | oL h1 =>
          simp only [n0] at hn
          obtain ⟨q, hq, e⟩ := tvn_O h
          exact clean_of_dig e (Px _ _ (by omega) (TVn.succ h1 hq))
    · -- t = O
      refine ⟨?_, ?_, ?_⟩
      · intro n r hn h
        simp only [nx] at hn
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        obtain ⟨a, ha, hr⟩ := TVn.succ_inv h
        cases ha with
        | axO _ =>
          obtain ⟨q, hq, e⟩ := tvn_O hr
          exact clean_of_dig e (Px _ _ (by omega) hq)
      · intro e he n r hn h
        cases he with
        | hO _ =>
          simp only [ne] at hn
          exact P1 _ _ hn h
      · intro e he n r _ h
        cases he with
        | oO _ => exact clean_tvn h (clean_cons (Or.inl rfl) hw)
    · -- t = I
      refine ⟨?_, ?_, ?_⟩
      · intro n r hn h
        simp only [nx] at hn
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        obtain ⟨a, ha, hr⟩ := TVn.succ_inv h
        cases ha with
        | axI he =>
          obtain ⟨q1, rfl, hq1⟩ := tvn_L n' hr
          obtain ⟨q2, hq2, e⟩ := tvn_O hq1
          rw [show 2 * n' / 2 = n' by omega] at hq2
          exact clean_cons (Or.inl rfl) (clean_of_dig e (Pe _ he _ _ (by omega) hq2))
      · intro e he n r hn h
        cases he with
        | hI he' =>
          simp only [ne] at hn
          exact P0 _ he' _ _ hn h
      · intro e he n r hn h
        cases he with
        | oI _ =>
          simp only [n0] at hn
          obtain ⟨q, hq, e⟩ := tvn_O h
          exact clean_of_dig e (P1 _ _ (by omega) hq)

/-- If the defect `x` in front of a clean tape needs at most one visit, the round's visit of A kills it. -/
theorem dies {W a} (hW : Clean W) (hn : nx W ≤ 1) (h : TV .A (.x :: W) a) : Clean a :=
  (fuel W hW).1 1 a hn (TVn.one h)

/-! ## The tape that round 8 leaves -/

/-- `A(S_8)`, the clean tape that round 8 leaves (round 9 starts with `x a9`). -/
def a9 : List T := [.L, .L, .L, .L, .O, .L, .L, .L, .I, .L, .I, .L, .I, .L, .O, .O, .I, .O, .I, .I]

theorem a9_clean : Clean a9 := by
  intro t ht; simp only [a9, List.mem_cons, List.not_mem_nil] at ht; rcases ht with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp_all


/-! ## The round tapes from round 9 on -/

/-- The round tapes from round 9 on: `R9 W` means that `x W` is the tape at the start of a round. -/
inductive R9 : List T → Prop
  | base : R9 a9
  | next {W a} : R9 W → TV .A (.x :: W) a → R9 a

theorem r9_clean (H : ∀ W, R9 W → nx W ≤ 1) {W} (h : R9 W) : Clean W := by
  induction h with
  | base => exact a9_clean
  | next hW ha ih => exact dies ih (H _ hW) ha

/-- The first round is fine: round 9's defect needs one visit. -/
theorem need_a9 : nx a9 ≤ 1 := by decide

end F36869
