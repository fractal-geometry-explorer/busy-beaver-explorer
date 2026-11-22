import Visit

namespace H28035

open TM

/-- `n` visits in a row turn `s` into `s'`. -/
def VisN : Nat → Tape → Tape → Prop
  | 0, s, s' => s' = s
  | n + 1, s, s' => ∃ s1, Vis s s1 ∧ VisN n s1 s'

/-- One of `n` visits in a row halts the machine. -/
def VisNHalts : Nat → Tape → Prop
  | 0, _ => False
  | n + 1, s => VisHalts s ∨ ∃ s1, Vis s s1 ∧ VisNHalts n s1

theorem visN_add : ∀ (a : Nat) {b : Nat} {s s1 s2 : Tape}, VisN a s s1 → VisN b s1 s2 → VisN (a + b) s s2
  | 0, b, s, s1, s2, h1, h2 => by
      simp only [VisN] at h1; subst h1; simpa using h2
  | a + 1, b, s, s1, s2, h1, h2 => by
      obtain ⟨t, ht, h1'⟩ := h1
      have := visN_add a h1' h2
      rw [show a + 1 + b = (a + b) + 1 by omega]
      exact ⟨t, ht, this⟩

theorem visNH_add : ∀ (a : Nat) {b : Nat} {s s1 : Tape}, VisN a s s1 → VisNHalts b s1 → VisNHalts (a + b) s
  | 0, b, s, s1, h1, h2 => by
      simp only [VisN] at h1; subst h1; simpa using h2
  | a + 1, b, s, s1, h1, h2 => by
      obtain ⟨t, ht, h1'⟩ := h1
      have := visNH_add a h1' h2
      rw [show a + 1 + b = (a + b) + 1 by omega]
      exact Or.inr ⟨t, ht, this⟩

/-- The digit cell after `n` visits to a digit block. -/
def bit (n : Nat) : Bool := n % 2 == 1

/-- `n` visits to `000 s`: the block shows the parity of `n`, and `n / 2` visits go on to `s`. -/
theorem visN_digit : ∀ (n : Nat) {s s' : Tape}, VisN (n / 2) s s' →
    VisN n (cons false (cons false (cons false s))) (cons (bit n) (cons false (cons false s')))
  | 0, s, s', h => by simp only [VisN] at h ⊢; subst h; rfl
  | 1, s, s', h => by
      simp only [VisN] at h ⊢; subst h
      exact ⟨_, vis_0, rfl⟩
  | n + 2, s, s', h => by
      rw [show (n + 2) / 2 = n / 2 + 1 by omega] at h
      obtain ⟨s1, h1, h'⟩ := h
      have ih := visN_digit n h'
      have hb : bit (n + 2) = bit n := by simp [bit, Nat.add_mod_right]
      rw [hb]
      exact ⟨_, vis_0, _, vis_100 h1, ih⟩

/-- A halting nested visit among the first `n / 2` makes one of `n` visits to `000 s` halt. -/
theorem visNH_digit : ∀ (n : Nat) {s : Tape}, VisNHalts (n / 2) s →
    VisNHalts n (cons false (cons false (cons false s)))
  | 0, s, h => by simp [VisNHalts] at h
  | 1, s, h => by simp [VisNHalts] at h
  | n + 2, s, h => by
      rw [show (n + 2) / 2 = n / 2 + 1 by omega] at h
      rcases h with h | ⟨s1, h1, h'⟩
      · exact Or.inr ⟨_, vis_0, Or.inl (vis_100_halts_1 h)⟩
      · exact Or.inr ⟨_, vis_0, Or.inr ⟨_, vis_100 h1, visNH_digit n h'⟩⟩

/-- `n` visits to `1010 s` make `2 n` visits to `s`. -/
theorem visN_L : ∀ (n : Nat) {s s' : Tape}, VisN (2 * n) s s' →
    VisN n (cons true (cons false (cons true (cons false s)))) (cons true (cons false (cons true (cons false s'))))
  | 0, s, s', h => by simp only [VisN] at h ⊢; subst h; rfl
  | n + 1, s, s', h => by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega] at h
      obtain ⟨s1, h1, s2, h2, h'⟩ := h
      exact ⟨_, vis_1010 h1 h2, visN_L n h'⟩

theorem visNH_L : ∀ (n : Nat) {s : Tape}, VisNHalts (2 * n) s →
    VisNHalts n (cons true (cons false (cons true (cons false s))))
  | 0, s, h => by simp [VisNHalts] at h
  | n + 1, s, h => by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega] at h
      rcases h with h | ⟨s1, h1, h | ⟨s2, h2, h'⟩⟩
      · exact Or.inl (vis_1010_halts_1 h)
      · exact Or.inl (vis_1010_halts_2 h1 h)
      · exact Or.inr ⟨_, vis_1010 h1 h2, visNH_L n h'⟩

theorem app_append_false (w : List Bool) : app (w ++ [false]) blank = app w blank := by
  induction w with
  | nil => simp [app, cons_false_blank]
  | cons a w ih => simp [app] at ih ⊢; rw [ih]

/-- The result of a computation on words. -/
inductive Res where
  | ok (w : List Bool)
  | halt
  | stuck
  deriving DecidableEq, Repr

/-- `visc f n w`: `n` visits to the stream `w 0^∞`, computed on the word with exact counts (`f` is fuel).
`ok w'`: the stream is now `w' 0^∞`; `halt`: one of the visits halts the machine (`1111`); `stuck`: out of fuel, or a
visit meets `11100`, which has no proved rule. -/
def visc : Nat → Nat → List Bool → Res
  | 0, _, _ => .stuck
  | _ + 1, 0, w => .ok w
  | f + 1, n + 1, w =>
    match w with
    | false :: s => visc f n (true :: s)
    | true :: false :: false :: s =>
      match visc f (1 + n / 2) s with
      | .ok s' => .ok (bit n :: false :: false :: s')
      | r => r
    | true :: true :: false :: s =>
      match visc f (1 + n / 2) s with
      | .ok s' => .ok (bit n :: false :: false :: s')
      | r => r
    | true :: false :: true :: false :: s =>
      match visc f (2 * (n + 1)) s with
      | .ok s' => .ok (true :: false :: true :: false :: s')
      | r => r
    | true :: false :: true :: true :: s => visc f n (false :: false :: false :: true :: s)
    | true :: true :: true :: true :: _ => .halt
    | true :: true :: true :: false :: true :: s => visc f n (true :: false :: true :: false :: true :: s)
    | true :: true :: true :: false :: false :: _ => .stuck
    | w => visc f (n + 1) (w ++ [false])

/-- After a first visit to `100 s` or `110 s`, the other `n` visits: `1 + n / 2` visits go on to `s`. -/
theorem visN_first (n : Nat) {a : Bool} {s s' : Tape}
    (h0 : ∀ {s s1 : Tape}, Vis s s1 → Vis (cons true (cons a (cons false s))) (cons false (cons false (cons false s1))))
    (h : VisN (1 + n / 2) s s') :
    VisN (n + 1) (cons true (cons a (cons false s))) (cons (bit n) (cons false (cons false s'))) := by
  rw [Nat.add_comm] at h
  obtain ⟨s1, h1, h'⟩ := h
  exact ⟨_, h0 h1, visN_digit n h'⟩

theorem visNH_first (n : Nat) {a : Bool} {s : Tape}
    (h0 : ∀ {s s1 : Tape}, Vis s s1 → Vis (cons true (cons a (cons false s))) (cons false (cons false (cons false s1))))
    (h0h : ∀ {s : Tape}, VisHalts s → VisHalts (cons true (cons a (cons false s))))
    (h : VisNHalts (1 + n / 2) s) :
    VisNHalts (n + 1) (cons true (cons a (cons false s))) := by
  rw [Nat.add_comm] at h
  rcases h with h | ⟨s1, h1, h'⟩
  · exact Or.inl (h0h h)
  · exact Or.inr ⟨_, h0 h1, visNH_digit n h'⟩

theorem visc_sound : ∀ (f n : Nat) (w : List Bool),
    (∀ w', visc f n w = .ok w' → VisN n (app w blank) (app w' blank)) ∧
    (visc f n w = .halt → VisNHalts n (app w blank))
  | 0, n, w => by simp [visc]
  | f + 1, 0, w => by simp [visc, VisN]
  | f + 1, n + 1, w => by
    match w with
    | false :: s =>
      obtain ⟨ih1, ih2⟩ := visc_sound f n (true :: s)
      refine ⟨fun w' h => ?_, fun h => ?_⟩
      · exact ⟨_, vis_0, ih1 w' (by simpa [visc] using h)⟩
      · exact Or.inr ⟨_, vis_0, ih2 (by simpa [visc] using h)⟩
    | true :: false :: false :: s =>
      obtain ⟨ih1, ih2⟩ := visc_sound f (1 + n / 2) s
      cases e : visc f (1 + n / 2) s with
      | ok s' =>
        refine ⟨fun w' h => ?_, fun h => ?_⟩
        · simp only [visc, e, Res.ok.injEq] at h; subst h
          exact visN_first n (fun h => vis_100 h) (ih1 s' e)
        · simp [visc, e] at h
      | halt =>
        refine ⟨fun w' h => ?_, fun _ => ?_⟩
        · simp [visc, e] at h
        · exact visNH_first n (fun h => vis_100 h) (fun h => vis_100_halts_1 h) (ih2 e)
      | stuck => simp [visc, e]
    | true :: true :: false :: s =>
      obtain ⟨ih1, ih2⟩ := visc_sound f (1 + n / 2) s
      cases e : visc f (1 + n / 2) s with
      | ok s' =>
        refine ⟨fun w' h => ?_, fun h => ?_⟩
        · simp only [visc, e, Res.ok.injEq] at h; subst h
          exact visN_first n (fun h => vis_110 h) (ih1 s' e)
        · simp [visc, e] at h
      | halt =>
        refine ⟨fun w' h => ?_, fun _ => ?_⟩
        · simp [visc, e] at h
        · exact visNH_first n (fun h => vis_110 h) (fun h => vis_110_halts_1 h) (ih2 e)
      | stuck => simp [visc, e]
    | true :: false :: true :: false :: s =>
      obtain ⟨ih1, ih2⟩ := visc_sound f (2 * (n + 1)) s
      cases e : visc f (2 * (n + 1)) s with
      | ok s' =>
        refine ⟨fun w' h => ?_, fun h => ?_⟩
        · simp only [visc, e, Res.ok.injEq] at h; subst h
          exact visN_L (n + 1) (ih1 s' e)
        · simp [visc, e] at h
      | halt =>
        refine ⟨fun w' h => ?_, fun _ => ?_⟩
        · simp [visc, e] at h
        · exact visNH_L (n + 1) (ih2 e)
      | stuck => simp [visc, e]
    | true :: false :: true :: true :: s =>
      obtain ⟨ih1, ih2⟩ := visc_sound f n (false :: false :: false :: true :: s)
      refine ⟨fun w' h => ?_, fun h => ?_⟩
      · exact ⟨_, vis_1011, ih1 w' (by simpa [visc] using h)⟩
      · exact Or.inr ⟨_, vis_1011, ih2 (by simpa [visc] using h)⟩
    | true :: true :: true :: true :: s =>
      refine ⟨fun w' h => ?_, fun _ => ?_⟩
      · simp [visc] at h
      · exact Or.inl vis_1111_halts
    | true :: true :: true :: false :: true :: s =>
      obtain ⟨ih1, ih2⟩ := visc_sound f n (true :: false :: true :: false :: true :: s)
      refine ⟨fun w' h => ?_, fun h => ?_⟩
      · exact ⟨_, vis_11101, ih1 w' (by simpa [visc] using h)⟩
      · exact Or.inr ⟨_, vis_11101, ih2 (by simpa [visc] using h)⟩
    | true :: true :: true :: false :: false :: s =>
      refine ⟨fun w' h => ?_, fun h => ?_⟩ <;> simp [visc] at h
    | [] =>
      have hv : visc (f + 1) (n + 1) [] = visc f (n + 1) ([] ++ [false]) := rfl
      obtain ⟨ih1, ih2⟩ := visc_sound f (n + 1) ([] ++ [false])
      rw [app_append_false] at ih1 ih2
      rw [hv]; exact ⟨ih1, ih2⟩
    | [true] =>
      have hv : visc (f + 1) (n + 1) [true] = visc f (n + 1) ([true] ++ [false]) := rfl
      obtain ⟨ih1, ih2⟩ := visc_sound f (n + 1) ([true] ++ [false])
      rw [app_append_false] at ih1 ih2
      rw [hv]; exact ⟨ih1, ih2⟩
    | [true, false] =>
      have hv : visc (f + 1) (n + 1) [true, false] = visc f (n + 1) ([true, false] ++ [false]) := rfl
      obtain ⟨ih1, ih2⟩ := visc_sound f (n + 1) ([true, false] ++ [false])
      rw [app_append_false] at ih1 ih2
      rw [hv]; exact ⟨ih1, ih2⟩
    | [true, true] =>
      have hv : visc (f + 1) (n + 1) [true, true] = visc f (n + 1) ([true, true] ++ [false]) := rfl
      obtain ⟨ih1, ih2⟩ := visc_sound f (n + 1) ([true, true] ++ [false])
      rw [app_append_false] at ih1 ih2
      rw [hv]; exact ⟨ih1, ih2⟩
    | [true, false, true] =>
      have hv : visc (f + 1) (n + 1) [true, false, true] = visc f (n + 1) ([true, false, true] ++ [false]) := rfl
      obtain ⟨ih1, ih2⟩ := visc_sound f (n + 1) ([true, false, true] ++ [false])
      rw [app_append_false] at ih1 ih2
      rw [hv]; exact ⟨ih1, ih2⟩
    | [true, true, true] =>
      have hv : visc (f + 1) (n + 1) [true, true, true] = visc f (n + 1) ([true, true, true] ++ [false]) := rfl
      obtain ⟨ih1, ih2⟩ := visc_sound f (n + 1) ([true, true, true] ++ [false])
      rw [app_append_false] at ih1 ih2
      rw [hv]; exact ⟨ih1, ih2⟩
    | [true, true, true, false] =>
      have hv : visc (f + 1) (n + 1) [true, true, true, false] = visc f (n + 1) ([true, true, true, false] ++ [false]) := rfl
      obtain ⟨ih1, ih2⟩ := visc_sound f (n + 1) ([true, true, true, false] ++ [false])
      rw [app_append_false] at ih1 ih2
      rw [hv]; exact ⟨ih1, ih2⟩

/-- A round, with at least one step. -/
theorem round_pos {s s' : Tape} (h : Vis (cons true (cons false s)) s') :
    ∃ n, 1 ≤ n ∧ steps n (LE s) = some (LE s') := by
  obtain ⟨n1, e1⟩ := h (true) (blank)
  have a0 : steps 6 ⟨cons false (cons false (blank)), cons true (cons false s), .A⟩ =
      some ⟨cons false (cons true (blank)), cons true (cons false s), .C⟩ := rfl
  rw [blank_eq] at a0
  exact ⟨6 + n1, by omega, steps_seq trans a0 e1⟩

/-- A round on words: put `1 0` in front of the word and make one visit. -/
def roundW (f : Nat) (w : List Bool) : Res := visc f 1 (true :: false :: w)

/-- The word after `k` rounds (fuel `f` for each round). -/
def run (f : Nat) : Nat → Res
  | 0 => .ok [true]
  | k + 1 =>
    match run f k with
    | .ok w => roundW f w
    | r => r

theorem halts_of_steps {n : Nat} {c c' : Config} (h : steps n c = some c') (h' : TM.Halts trans c') :
    TM.Halts trans c := by
  obtain ⟨m, c'', e, hc⟩ := h'
  exact ⟨n + m, c'', steps_seq trans h e, hc⟩

/-- What `run` computes is what the machine does: after `k` rounds the tape is `0^∞ A> 1 0 w 0^∞`, reached after
at least `k` steps, and a `halt` means the machine halts. -/
theorem run_sound (f : Nat) : ∀ k,
    (∀ w, run f k = .ok w → ∃ n, k ≤ n ∧ steps n init = some (LE (app w blank))) ∧
    (run f k = .halt → HaltsFromBlank)
  | 0 => by
    refine ⟨fun w h => ?_, fun h => ?_⟩
    · simp only [run, Res.ok.injEq] at h; subst h
      exact ⟨4, by omega, start⟩
    · simp [run] at h
  | k + 1 => by
    obtain ⟨ih1, ih2⟩ := run_sound f k
    cases e : run f k with
    | ok w =>
      obtain ⟨n, hn, hs⟩ := ih1 w e
      obtain ⟨v1, v2⟩ := visc_sound f 1 (true :: false :: w)
      refine ⟨fun w' h => ?_, fun h => ?_⟩
      · simp only [run, e] at h
        obtain ⟨s1, hv, hs1⟩ := v1 w' h
        simp only [VisN] at hs1
        subst hs1
        obtain ⟨m, hm, hr⟩ := round_pos hv
        exact ⟨n + m, by omega, steps_seq trans hs hr⟩
      · simp only [run, e] at h
        rcases v2 h with hh | ⟨_, _, hh⟩
        · exact halts_of_steps hs (round_halts hh)
        · exact hh.elim
    | halt =>
      refine ⟨fun w' h => ?_, fun _ => ih2 e⟩
      simp [run, e] at h
    | stuck =>
      refine ⟨fun w' h => ?_, fun h => ?_⟩ <;> simp [run, e] at h

/-- If the computation on words ever reports `halt`, the machine halts from blank tape. -/
theorem halts_of_run {f k : Nat} (h : run f k = .halt) : HaltsFromBlank :=
  (run_sound f k).2 h

/-- If every number of rounds can be computed on words without `halt`, the machine never halts. -/
theorem not_halts_of_run (h : ∀ k, ∃ f w, run f k = .ok w) : ¬ HaltsFromBlank := by
  apply TM.not_halts_of_forall
  apply TM.forall_of_unbounded trans (fun m => ∃ c', steps m init = some c')
  · intro n
    obtain ⟨f, w, hw⟩ := h n
    obtain ⟨m, hm, hs⟩ := (run_sound f n).1 w hw
    exact ⟨m, hm, _, hs⟩
  · exact fun m hm => hm

/-! ## After a junk event

A count that runs out with one visit on the last `0` before a block starting with `1` leaves `0 1 1` in the word
(the only way two `1`s can touch). The next round enters the digit block that ends just before it at offset 1 or 2,
so its next visits meet `0 0 1 1 …` or `0 1 1 …`. -/

/-- Offset 1: two visits to `0 0 1 1 s` give `0 0 0 1 s` (the second through `1011`); nothing nested. -/
theorem junk_offset1 {s : Tape} :
    VisN 2 (cons false (cons false (cons true (cons true s)))) (cons false (cons false (cons false (cons true s)))) :=
  ⟨_, vis_0, _, vis_1011, rfl⟩

/-- Offset 2: the first of two visits to `0 1 1 s` gives `1 1 1 s`; at the word end `s` is `0 0 …`, and `11100` has no
proved rule (`visc` reports `stuck`). -/
theorem junk_offset2_first {s : Tape} : Vis (cons false (cons true (cons true s))) (cons true (cons true (cons true s))) :=
  vis_0

end H28035
