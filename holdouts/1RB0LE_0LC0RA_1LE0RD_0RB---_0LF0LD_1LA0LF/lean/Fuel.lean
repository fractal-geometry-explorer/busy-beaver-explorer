import Link

/-! # How many visits a defect needs, and the reduction corrected to start at round 9

Machine: 1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF, read on the mirrored tape (see the README of this folder and
`Tokens.lean`, `Total.lean`, `Link.lean`, which this file builds on).

* `nx`, `ne`, `n0`: the **fuel** a defect needs. `nx W` is a number of visits of A after which `x W` (W a tape of
  words) has no defect left; `ne`, `n0` are the same for the tapes that `Eh` and `E0` leave. They are computed by a
  plain recursion over the words of W (`nx (O W) = 2 nx W + 1`, `nx (L W) = ⌈nx W / 2⌉`, `nx (I W) = ne W + 1`, ...),
  so whether a defect dies is decided by the tape it sits on, without running the visits.
* `fuel`: if `nx W ≤ n`, then n visits of A on `x W` leave a clean tape (and the same for `1 W`, and for the tapes
  of `Eh`, `E0`). In particular `dies`: if `nx W ≤ 1`, the round's single visit kills the defect `x` put in front.
* `old_hyp_false`: the hypothesis of `L36869.nonhalt_of_clean` (every round's defect dies, counted from blank tape)
  is false: the defect of round 2 survives (`A(x L O I) = L I x I`). The early rounds are not one-defect tapes, so
  that theorem was vacuous.
* `round9`: the machine reaches the start of round 9, `0 x A(S_8)` with `A(S_8)` the clean tape `a9` below, at step
  5,848 from blank tape (kernel evaluation).
* `nonhalt_of_need`: the corrected reduction. If for every round from 9 on the defect needs at most one visit
  (`nx W ≤ 1` on the round's tape `x W`), the machine never halts from blank tape.

What is left open is exactly the hypothesis of `nonhalt_of_need`. In the run the margin is huge: the round tape is
`x L^m U`, so `nx (L^m U) = ⌈nx U / 2^m⌉`, and `nx U = 3` in every round from 12 to 3,000 that was checked
(`py/fuel.py`), against `2^m` with m about k/2.
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

/-! ## The old reduction was vacuous -/

/-- The hypothesis of `L36869.nonhalt_of_clean` is false: from blank tape, `S_2 = x L O I` and the defect survives
round 2 (`A(x L O I) = L I x I`). -/
theorem old_hyp_false : ¬ (∀ w a, L36869.Reach w → TV .A w a → Clean a) := by
  intro H
  have r1 : L36869.Reach [.x, .I] := L36869.Reach.next L36869.Reach.nil TV.aNil
  have r2 : L36869.Reach [.x, .L, .O, .I] := L36869.Reach.next r1 (TV.axI TV.hNil)
  have t2 : TV .A [.x, .L, .O, .I] [.L, .I, .x, .I] := TV.axL (TV.axO [.I]) (TV.aO [.x, .I])
  have hx := H _ _ r2 t2 .x (by simp)
  simp at hx

/-! ## Round 9, reached from blank tape -/

/-- `A(S_8)`, the clean tape that round 8 leaves (round 9 starts with `x a9`). -/
def a9 : List T := [.L, .L, .L, .L, .O, .L, .L, .L, .I, .L, .I, .L, .I, .L, .O, .O, .I, .O, .I, .I]

theorem a9_clean : Clean a9 := by
  intro t ht; simp only [a9, List.mem_cons, List.not_mem_nil] at ht; rcases ht with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp_all

/-- The bits of a word list, head first. -/
def flat : List T → List Bool
  | [] => []
  | t :: w => bits t ++ flat w

theorem pre_eq (l : List Bool) (s : Tape) : pre l s = TM.app l s := by
  induction l with
  | nil => rfl
  | cons b l ih => show Z36869.cons b (pre l s) = TM.cons b (TM.app l s); rw [ih, L36869.zc]

theorem enc_eq (w : List T) : enc w = TM.app (flat w) TM.blank := by
  induction w with
  | nil => rfl
  | cons t w ih => show pre (bits t) (enc w) = _; rw [pre_eq, ih, flat, TM.app_app]

/-- The left half tape at the start of round 9, as the list simulator leaves it (no trailing blanks). -/
def l9 : List Bool := (false :: flat (.x :: a9)).dropLast.dropLast

theorem l9_eq : false :: flat (.x :: a9) = l9 ++ [false, false] := by decide

theorem round9_f : H36869.fsteps 5848 (TM.FCfg.blank .A) = some ⟨l9, [false], .A⟩ := by decide +kernel

/-- From blank tape the machine reaches the start of round 9 at step 5,848. -/
theorem round9 : H36869.steps 5848 H36869.init = some ⟨TM.cons false (enc (.x :: a9)), TM.blank, .A⟩ := by
  have h := TM.blank_reaches H36869.trans round9_f
  show TM.steps H36869.trans 5848 (TM.blankCfg .A) = _
  rw [h]
  have e1 : TM.app l9 TM.blank = TM.cons false (enc (.x :: a9)) := by
    rw [enc_eq, ← TM.app_cons, l9_eq, ← TM.app_app]
    show TM.app l9 TM.blank = TM.app l9 (TM.cons false (TM.cons false TM.blank))
    rw [TM.cons_false_blank, TM.cons_false_blank]
  have e2 : TM.app [false] TM.blank = TM.blank := TM.cons_false_blank
  show some (⟨TM.app l9 TM.blank, TM.app [false] TM.blank, .A⟩ : H36869.Config) = _
  rw [e1, e2]

/-! ## The corrected reduction -/

/-- The round tapes from round 9 on: `R9 W` means that `x W` is the tape at the start of a round. -/
inductive R9 : List T → Prop
  | base : R9 a9
  | next {W a} : R9 W → TV .A (.x :: W) a → R9 a

theorem r9_clean (H : ∀ W, R9 W → nx W ≤ 1) {W} (h : R9 W) : Clean W := by
  induction h with
  | base => exact a9_clean
  | next hW ha ih => exact dies ih (H _ hW) ha

theorem runs9 (H : ∀ W, R9 W → nx W ≤ 1) :
    ∀ k, ∃ W n, R9 W ∧ k ≤ n ∧ H36869.steps n H36869.init = some ⟨TM.cons false (enc (.x :: W)), TM.blank, .A⟩ := by
  intro k
  induction k with
  | zero => exact ⟨a9, 5848, R9.base, by omega, round9⟩
  | succ k ih =>
    obtain ⟨W, n, hW, hk, hn⟩ := ih
    have hg : Good (.x :: W) := Or.inr ⟨[], .x, W, clean_nil, Or.inl rfl, r9_clean H hW, rfl⟩
    obtain ⟨a, ha⟩ := L36869.step_of_good hg
    have hv : L36869.Vis .A (enc (.x :: W)) (enc a) := L36869.link (sound ha)
    obtain ⟨m, hm1, hm⟩ := L36869.round hv
    refine ⟨a, n + m, R9.next hW ha, by omega, ?_⟩
    rw [L36869.enc_x]; exact L36869.seq hn hm

/-- **The corrected reduction.** If in every round from round 9 on the defect in front needs at most one visit
(`nx W ≤ 1` on the round tape `x W`), the machine never halts from blank tape. -/
theorem nonhalt_of_need (H : ∀ W, R9 W → nx W ≤ 1) : ¬ H36869.HaltsFromBlank := by
  apply TM.not_halts_of_forall
  apply TM.forall_of_unbounded _ (fun m => ∃ W, H36869.steps m H36869.init =
    some ⟨TM.cons false (enc (.x :: W)), TM.blank, .A⟩)
  · intro n
    obtain ⟨W, m, _, hm, h⟩ := runs9 H n
    exact ⟨m, hm, W, h⟩
  · rintro m ⟨W, h⟩
    exact ⟨_, h⟩

/-- The first round is fine: round 9's defect needs one visit. -/
theorem need_a9 : nx a9 ≤ 1 := by decide

end F36869
