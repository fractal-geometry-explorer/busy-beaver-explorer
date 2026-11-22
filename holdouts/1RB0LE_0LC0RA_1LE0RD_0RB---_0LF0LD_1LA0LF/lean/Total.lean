import Tokens

/-! # A tape with at most one defect cannot halt

Machine: 1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF, read on the mirrored tape (see the README of this folder and
`Tokens.lean`, whose token rules `TV` and their soundness `sound` this file builds on).

The README argued by hand that the token rules apply to every tape with one defect, so that such a tape cannot
halt. This file proves it in the kernel:

* `det`: the token rules are deterministic (each visit has at most one result).
* `total`: on every token tape with **at most one** defect (`Good`: words `L`, `O`, `I` and at most one of the
  defects `x`, `1`, `z`), any number of visits of A in a row are derived by the token rules, and every
  intermediate tape again has at most one defect.
* `total_bits`: the same at the bit level: each of those visits is a computation of the four visit functions
  (`BV`), none of which is the halting case `E(1 1 T)`.

So during a round the machine can only halt if the tape holds two defects. Each round adds one defect at the front
(`S' = 1 0 A(S)`), so a halt needs the defect of some round to survive to the end of that round. What is still
not proved is exactly that: that every round's defect disappears. (The link between the four visit functions and
the transition table, and the round law, are proved in `Link.lean`.)
-/

namespace Z36869

/-! ## Determinism -/

theorem det {k w a b} (h1 : TV k w a) (h2 : TV k w b) : a = b := by
  induction h1 generalizing b with
  | aL _ _ ih1 ih2 => cases h2 with
    | aL h h' => cases ih1 h; rw [ih2 h']
  | aO w => cases h2; rfl
  | aI _ ih => cases h2 with
    | aI h => rw [ih h]
  | aNil => cases h2; rfl
  | az w => cases h2; rfl
  | axO w => cases h2; rfl
  | axI _ ih => cases h2 with
    | axI h => rw [ih h]
  | axL _ _ ih1 ih2 => cases h2 with
    | axL h h' => cases ih1 h; rw [ih2 h']
  | a1 _ ih => cases h2 with
    | a1 h => rw [ih h]
  | axEnd _ ih => cases h2 with
    | axEnd h => exact ih h
  | hL _ ih => cases h2 with
    | hL h => rw [ih h]
  | hO w => cases h2; rfl
  | hI _ ih => cases h2 with
    | hI h => exact ih h
  | hNil => cases h2; rfl
  | oO w => cases h2; rfl
  | oL _ ih => cases h2 with
    | oL h => rw [ih h]
  | oI w => cases h2; rfl
  | oNil => cases h2; rfl

/-! ## Visits in a row -/

/-- `TVn n w r`: n visits of A in a row take `w` to `r`. -/
inductive TVn : Nat → List T → List T → Prop
  | zero (w) : TVn 0 w w
  | succ {n w a r} : TV .A w a → TVn n a r → TVn (n + 1) w r

theorem TVn.zero_inv {w r} (h : TVn 0 w r) : r = w := by cases h; rfl

theorem TVn.succ_inv {n w r} (h : TVn (n + 1) w r) : ∃ a, TV .A w a ∧ TVn n a r := by
  cases h with
  | succ h1 h2 => exact ⟨_, h1, h2⟩

theorem TVn.trans {m n w a r} (h1 : TVn m w a) (h2 : TVn n a r) : TVn (m + n) w r := by
  induction h1 with
  | zero => simpa using h2
  | succ h _ ih =>
    have e : ∀ p q : Nat, p + 1 + q = (p + q) + 1 := by intros; omega
    rw [e]; exact TVn.succ h (ih h2)

theorem TVn.split {m n w r} (h : TVn (m + n) w r) : ∃ a, TVn m w a ∧ TVn n a r := by
  induction m generalizing w with
  | zero => exact ⟨w, TVn.zero w, by simpa using h⟩
  | succ m ih =>
    have e : m + 1 + n = (m + n) + 1 := by omega
    rw [e] at h
    obtain ⟨a, ha, hr⟩ := TVn.succ_inv h
    obtain ⟨b, hb, hb'⟩ := ih hr
    exact ⟨b, TVn.succ ha hb, hb'⟩

theorem TVn.one {w a} (h : TV .A w a) : TVn 1 w a := TVn.succ h (TVn.zero a)

/-! ## Tapes with at most one defect -/

/-- Only words: `L`, `O`, `I`. -/
def Clean (w : List T) : Prop := ∀ t ∈ w, t = .L ∨ t = .O ∨ t = .I

/-- The defects. -/
def Mark (d : T) : Prop := d = .x ∨ d = .one ∨ d = .z

/-- Words and at most one defect. -/
def Good (w : List T) : Prop := Clean w ∨ ∃ p d s, Clean p ∧ Mark d ∧ Clean s ∧ w = p ++ d :: s

/-- Every number of visits in a row is derived, and every result has at most one defect. -/
def Fine (w : List T) : Prop := ∀ n, ∃ r, TVn n w r ∧ Good r

theorem clean_nil : Clean [] := by intro t ht; cases ht

theorem clean_cons {t w} (ht : t = .L ∨ t = .O ∨ t = .I) (h : Clean w) : Clean (t :: w) := by
  intro u hu
  cases hu with
  | head => exact ht
  | tail _ hu => exact h u hu

theorem clean_tail {t w} (h : Clean (t :: w)) : Clean w := fun u hu => h u (List.Mem.tail _ hu)

theorem clean_head {t w} (h : Clean (t :: w)) : t = .L ∨ t = .O ∨ t = .I := h t (List.Mem.head _)

theorem good_cons {t w} (ht : t = .L ∨ t = .O ∨ t = .I) (h : Good w) : Good (t :: w) := by
  rcases h with h | ⟨p, d, s, hp, hd, hs, rfl⟩
  · exact Or.inl (clean_cons ht h)
  · exact Or.inr ⟨t :: p, d, s, clean_cons ht hp, hd, hs, rfl⟩

theorem good_mark {d s} (hd : Mark d) (hs : Clean s) : Good (d :: s) :=
  Or.inr ⟨[], d, s, clean_nil, hd, hs, rfl⟩

theorem fine_zero {w} (h : Fine w) : Good w := by
  obtain ⟨r, hr, hg⟩ := h 0
  rw [TVn.zero_inv hr] at hg; exact hg

theorem fine_step {w a} (h : Fine w) (ha : TV .A w a) : Fine a := by
  intro n
  obtain ⟨r, hr, hg⟩ := h (n + 1)
  obtain ⟨a', ha', hr'⟩ := TVn.succ_inv hr
  cases det ha ha'
  exact ⟨r, hr', hg⟩

/-! ## A word in front of a tape -/

theorem run_L : ∀ n {r q}, TVn (2 * n) r q → TVn n (.L :: r) (.L :: q)
  | 0, r, q, h => by rw [TVn.zero_inv h]; exact TVn.zero _
  | n + 1, r, q, h => by
    have e : 2 * (n + 1) = 2 + 2 * n := by omega
    rw [e] at h
    obtain ⟨b, hb, hq⟩ := TVn.split h
    obtain ⟨a, ha, hab⟩ := TVn.succ_inv hb
    obtain ⟨b', hb', h0⟩ := TVn.succ_inv hab
    obtain rfl := TVn.zero_inv h0
    exact TVn.succ (TV.aL ha hb') (run_L n hq)

theorem run_O : ∀ j {r q}, TVn j r q →
    TVn (2 * j) (.O :: r) (.O :: q) ∧ TVn (2 * j + 1) (.O :: r) (.I :: q)
  | 0, r, q, h => by
    rw [TVn.zero_inv h]; exact ⟨TVn.zero _, TVn.one (TV.aO _)⟩
  | j + 1, r, q, h => by
    obtain ⟨a, ha, hq⟩ := TVn.succ_inv h
    obtain ⟨h1, h2⟩ := run_O j hq
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 by omega, show 2 * (j + 1) = 2 * j + 1 + 1 by omega]
    exact ⟨TVn.succ (TV.aO r) (TVn.succ (TV.aI ha) h1), TVn.succ (TV.aO r) (TVn.succ (TV.aI ha) h2)⟩

theorem fine_cons {t r} (ht : t = .L ∨ t = .O ∨ t = .I) (h : Fine r) : Fine (t :: r) := by
  intro n
  rcases ht with rfl | rfl | rfl
  · obtain ⟨q, hq, hg⟩ := h (2 * n)
    exact ⟨_, run_L n hq, good_cons (Or.inl rfl) hg⟩
  · obtain ⟨q, hq, hg⟩ := h (n / 2)
    obtain ⟨h1, h2⟩ := run_O (n / 2) hq
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · have e : n = 2 * (n / 2) := by omega
      rw [e]; exact ⟨_, h1, good_cons (Or.inr (Or.inl rfl)) hg⟩
    · have e : n = 2 * (n / 2) + 1 := by omega
      rw [e]; exact ⟨_, h2, good_cons (Or.inr (Or.inr rfl)) hg⟩
  · cases n with
    | zero => exact ⟨_, TVn.zero _, good_cons (Or.inr (Or.inr rfl)) (fine_zero h)⟩
    | succ n =>
      obtain ⟨q, hq, hg⟩ := h (n / 2 + 1)
      obtain ⟨a, ha, haq⟩ := TVn.succ_inv hq
      obtain ⟨h1, h2⟩ := run_O (n / 2) haq
      rcases Nat.mod_two_eq_zero_or_one n with hn | hn
      · have e : n = 2 * (n / 2) := by omega
        rw [e]; exact ⟨_, TVn.succ (TV.aI ha) h1, good_cons (Or.inr (Or.inl rfl)) hg⟩
      · have e : n = 2 * (n / 2) + 1 := by omega
        rw [e]; exact ⟨_, TVn.succ (TV.aI ha) h2, good_cons (Or.inr (Or.inr rfl)) hg⟩

/-! ## Tapes without defects -/

/-- Only digits. -/
def Dig (w : List T) : Prop := ∀ t ∈ w, t = .O ∨ t = .I

theorem dig_clean {w} (h : Dig w) : Clean w := fun t ht => Or.inr (h t ht)

theorem dig_step : ∀ w, Dig w → ∃ a, TV .A w a ∧ Dig a
  | [], _ => ⟨[.I], TV.aNil, by intro t ht; simp at ht; exact Or.inr ht⟩
  | t :: w, h => by
    have hw : Dig w := fun u hu => h u (List.Mem.tail _ hu)
    rcases h t (List.Mem.head _) with rfl | rfl
    · refine ⟨.I :: w, TV.aO w, ?_⟩
      intro u hu; cases hu with
      | head => exact Or.inr rfl
      | tail _ hu => exact hw u hu
    · obtain ⟨a, ha, hd⟩ := dig_step w hw
      refine ⟨.O :: a, TV.aI ha, ?_⟩
      intro u hu; cases hu with
      | head => exact Or.inl rfl
      | tail _ hu => exact hd u hu

theorem fine_nil : Fine [] := by
  intro n
  suffices ∃ r, TVn n [] r ∧ Dig r by
    obtain ⟨r, hr, hd⟩ := this; exact ⟨r, hr, Or.inl (dig_clean hd)⟩
  induction n with
  | zero => exact ⟨[], TVn.zero _, fun t ht => by cases ht⟩
  | succ n ih =>
    obtain ⟨r, hr, hd⟩ := ih
    obtain ⟨a, ha, hd'⟩ := dig_step r hd
    exact ⟨a, TVn.trans hr (TVn.one ha), hd'⟩

theorem fine_clean : ∀ w, Clean w → Fine w
  | [], _ => fine_nil
  | _ :: w, h => fine_cons (clean_head h) (fine_clean w (clean_tail h))

/-! ## One defect -/

/-- What the induction on the length of the tape behind the defect proves. -/
def Three (s : List T) : Prop := Fine (.x :: s) ∧ Fine (.one :: s) ∧ Fine (.z :: s)

/-- `Eh` (the defect thrown ahead by `x I` and by `1`) on a clean tape gives a tape on which all visits work. -/
theorem eh_fine : ∀ s, Clean s → (∀ s', s'.length < s.length → Clean s' → Three s') →
    ∃ e, TV .Eh s e ∧ Fine e
  | [], _, _ => ⟨[.I], TV.hNil, fine_clean _ (clean_cons (Or.inr (Or.inr rfl)) clean_nil)⟩
  | t :: w, hc, H => by
    have hw := clean_tail hc
    rcases clean_head hc with rfl | rfl | rfl
    · obtain ⟨e, he, hf⟩ := eh_fine w hw (fun s' hl hs' => H s' (by simp only [List.length_cons]; omega) hs')
      exact ⟨.L :: e, TV.hL he, fine_cons (Or.inl rfl) hf⟩
    · exact ⟨.one :: w, TV.hO w, (H w (by simp only [List.length_cons]; omega) hw).2.1⟩
    · -- E0 on w
      match w, hw with
      | [], _ => exact ⟨[.L], TV.hI TV.oNil, fine_clean _ (clean_cons (Or.inl rfl) clean_nil)⟩
      | u :: w', hw =>
        have hw' := clean_tail hw
        rcases clean_head hw with rfl | rfl | rfl
        · have hx := (H w' (by simp only [List.length_cons]; omega) hw').1
          obtain ⟨a, ha, _⟩ := hx 1
          obtain ⟨a', ha', h0⟩ := TVn.succ_inv ha
          obtain rfl := TVn.zero_inv h0
          exact ⟨.O :: a, TV.hI (TV.oL ha'), fine_cons (Or.inr (Or.inl rfl)) (fine_step hx ha')⟩
        · exact ⟨.L :: w', TV.hI (TV.oO w'), fine_clean _ (clean_cons (Or.inl rfl) hw')⟩
        · exact ⟨.O :: .one :: w', TV.hI (TV.oI w'),
            fine_cons (Or.inr (Or.inl rfl)) (H w' (by simp only [List.length_cons]; omega) hw').2.1⟩

theorem three : ∀ m s, s.length < m → Clean s → Three s
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | m + 1, s, hl, hc => by
    have H : ∀ s', s'.length < s.length → Clean s' → Three s' :=
      fun s' h' hs' => three m s' (by omega) hs'
    -- the defect `1`
    have h1 : Fine (.one :: s) := by
      obtain ⟨e, he, hf⟩ := eh_fine s hc H
      intro n
      cases n with
      | zero => exact ⟨_, TVn.zero _, good_mark (Or.inr (Or.inl rfl)) hc⟩
      | succ n =>
        obtain ⟨r, hr, hg⟩ := fine_cons (Or.inr (Or.inl rfl)) hf n
        exact ⟨r, TVn.succ (TV.a1 he) hr, hg⟩
    -- the defect `z`
    have hz : Fine (.z :: s) := by
      intro n
      cases n with
      | zero => exact ⟨_, TVn.zero _, good_mark (Or.inr (Or.inr rfl)) hc⟩
      | succ n =>
        obtain ⟨r, hr, hg⟩ := h1 n
        exact ⟨r, TVn.succ (TV.az s) hr, hg⟩
    -- the defect `x`
    have hx : Fine (.x :: s) := by
      intro n
      cases n with
      | zero => exact ⟨_, TVn.zero _, good_mark (Or.inl rfl) hc⟩
      | succ n =>
        match s, hc, H with
        | [], _, _ =>
          have hI : TV .A [.I] [.O, .I] := TV.aI TV.aNil
          obtain ⟨r, hr, hg⟩ := fine_clean [.O, .I]
            (clean_cons (Or.inr (Or.inl rfl)) (clean_cons (Or.inr (Or.inr rfl)) clean_nil)) n
          exact ⟨r, TVn.succ (TV.axEnd hI) hr, hg⟩
        | t :: w, hc, H =>
          have hw := clean_tail hc
          rcases clean_head hc with rfl | rfl | rfl
          · -- x L w: L A(A(x w))
            obtain ⟨q, hq, hg⟩ := (H w (by simp only [List.length_cons]; omega) hw).1 (2 + 2 * n)
            obtain ⟨b, hb, hbq⟩ := TVn.split hq
            obtain ⟨a, ha, hab⟩ := TVn.succ_inv hb
            obtain ⟨b', hb', h0⟩ := TVn.succ_inv hab
            obtain rfl := TVn.zero_inv h0
            exact ⟨_, TVn.succ (TV.axL ha hb') (run_L n hbq), good_cons (Or.inl rfl) hg⟩
          · -- x O w: O x w
            obtain ⟨r, hr, hg⟩ := fine_cons (Or.inr (Or.inl rfl)) (H w (by simp only [List.length_cons]; omega) hw).1 n
            exact ⟨r, TVn.succ (TV.axO w) hr, hg⟩
          · -- x I w: L O Eh(w)
            obtain ⟨e, he, hf⟩ := eh_fine w hw (fun s' h' hs' => H s' (by simp only [List.length_cons]; omega) hs')
            obtain ⟨r, hr, hg⟩ :=
              fine_cons (Or.inl rfl) (fine_cons (Or.inr (Or.inl rfl)) hf) n
            exact ⟨r, TVn.succ (TV.axI he) hr, hg⟩
    exact ⟨hx, h1, hz⟩

/-- **Every tape with at most one defect**: any number of visits of A in a row are derived by the token rules, and
the tape keeps at most one defect. -/
theorem total {w} (h : Good w) : Fine w := by
  rcases h with h | ⟨p, d, s, hp, hd, hs, rfl⟩
  · exact fine_clean w h
  · have h3 := three (s.length + 1) s (Nat.lt_succ_self _) hs
    have hds : Fine (d :: s) := by
      rcases hd with rfl | rfl | rfl
      · exact h3.1
      · exact h3.2.1
      · exact h3.2.2
    induction p with
    | nil => exact hds
    | cons t p ih => exact fine_cons (clean_head hp) (ih (clean_tail hp))

/-- `n` visits of A in a row at the bit level. -/
inductive BVn : Nat → Tape → Tape → Prop
  | zero (s) : BVn 0 s s
  | succ {n s a r} : BV .A s a → BVn n a r → BVn (n + 1) s r

theorem bvn_of_tvn {n w r} (h : TVn n w r) : BVn n (enc w) (enc r) := by
  induction h with
  | zero w => exact BVn.zero _
  | succ h _ ih => exact BVn.succ (sound h) ih

/-- **At the bit level**: from a tape with at most one defect, the four visit functions return from any number of
visits of A in a row (none of their equations is the halting case `E(1 1 T)`), and each tape between them again
reads as words with at most one defect. -/
theorem total_bits {w} (h : Good w) (n : Nat) : ∃ r, BVn n (enc w) (enc r) ∧ Good r := by
  obtain ⟨r, hr, hg⟩ := total h n
  exact ⟨r, bvn_of_tvn hr, hg⟩

end Z36869
