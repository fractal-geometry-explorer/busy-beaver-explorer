import TM.Basic

/-!
# Halts-iff from a map on abstract states

A machine's run is often described by a map `next : S → Option S` on abstract states (counters, words): each state
stands for a set of configurations (`Rel s c`), and from every configuration of `s` the machine either reaches, in
at least one step, a configuration of `next s`, or halts (when `next s = none`).  Then the machine halts from `c₀` if
and only if the orbit of `next` from the first state stops (`halts_iff_orbit`).

`Plus`, `Star` and `HaltsFrom` are the run relations the proofs of such steps chain together.
-/

namespace TM

variable {Q : Type} (δ : Q → Bool → Option (Bool × Dir × Q))

/-- `c` reaches `c'` in one step or more. -/
def Plus (c c' : Cfg Q) : Prop := ∃ n, steps δ (n + 1) c = some c'

/-- `c` reaches `c'` in zero steps or more. -/
def Star (c c' : Cfg Q) : Prop := ∃ n, steps δ n c = some c'

variable {δ}

theorem Plus.star {c c' : Cfg Q} (h : Plus δ c c') : Star δ c c' := let ⟨n, hn⟩ := h; ⟨n + 1, hn⟩

theorem Plus.trans {a b c : Cfg Q} (h₁ : Plus δ a b) (h₂ : Plus δ b c) : Plus δ a c := by
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m + 1, by rw [show n + m + 1 + 1 = (n + 1) + (m + 1) by omega]; exact steps_seq δ hn hm⟩

theorem Plus.trans_star {a b c : Cfg Q} (h₁ : Plus δ a b) (h₂ : Star δ b c) : Plus δ a c := by
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, by rw [show n + m + 1 = (n + 1) + m by omega]; exact steps_seq δ hn hm⟩

theorem Star.trans_plus {a b c : Cfg Q} (h₁ : Star δ a b) (h₂ : Plus δ b c) : Plus δ a c := by
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, by rw [show n + m + 1 = n + (m + 1) by omega]; exact steps_seq δ hn hm⟩

theorem Star.trans {a b c : Cfg Q} (h₁ : Star δ a b) (h₂ : Star δ b c) : Star δ a c := by
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, steps_seq δ hn hm⟩

theorem Star.refl (c : Cfg Q) : Star δ c c := ⟨0, rfl⟩

/-- A run of `k ≥ 1` steps as `Plus`, up to equal start and end configurations. -/
theorem plus_of {k : Nat} {c c' d d' : Cfg Q} (h : steps δ k c = some d) (e₁ : c' = c) (e₂ : d = d')
    (hk : 0 < k := by omega) : Plus δ c' d' :=
  ⟨k - 1, by rw [show k - 1 + 1 = k by omega, e₁, h, e₂]⟩

/-- A run of `n` steps as `Star`, up to equal start and end configurations. -/
theorem star_of {n : Nat} {c c' d d' : Cfg Q} (h : steps δ n c = some d) (e₁ : c' = c) (e₂ : d = d') :
    Star δ c' d' := ⟨n, by rw [e₁, h, e₂]⟩

/-- A halting run, up to an equal start configuration. -/
theorem halts_at {n : Nat} {c c' d : Cfg Q} (h : steps δ n c = some d) (e : c' = c) (hd : step δ d = none) :
    Halts δ c' := ⟨n, d, by rw [e, h], hd⟩

theorem Halts.pre {c c' : Cfg Q} (h₁ : Star δ c c') (h₂ : Halts δ c') : Halts δ c := by
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, d, hm, hd⟩ := h₂
  exact ⟨n + m, d, steps_seq δ hn hm, hd⟩

section Orbit

variable {S : Type} (next : S → Option S) (Rel : S → Cfg Q → Prop)

/-- What a configuration does under the map's next value: reach a configuration of the next state, or halt. -/
def Lands (δ : Q → Bool → Option (Bool × Dir × Q)) (Rel : S → Cfg Q → Prop) (c : Cfg Q) : Option S → Prop
  | some s' => ∃ c', Plus δ c c' ∧ Rel s' c'
  | none => Halts δ c

/-- `n` steps of the map from `s₀`; `none` once it stops. -/
def orbit (s₀ : S) : Nat → Option S
  | 0 => some s₀
  | n + 1 => (orbit s₀ n).bind next

variable {next Rel}

theorem Lands.pre {c c' : Cfg Q} (h : Plus δ c c') : ∀ {o : Option S}, Lands δ Rel c' o → Lands δ Rel c o
  | some _, ⟨d, hd, hr⟩ => ⟨d, h.trans hd, hr⟩
  | none, h' => Halts.pre h.star h'

/-- **Halts-iff from a map.**  If the first state is reached from `c₀` and every state lands where `next` says, the
machine halts from `c₀` if and only if the orbit of `next` stops. -/
theorem halts_iff_orbit {c₀ : Cfg Q} {s₀ : S} (h₀ : ∃ t c, steps δ t c₀ = some c ∧ Rel s₀ c)
    (hstep : ∀ s c, Rel s c → Lands δ Rel c (next s)) :
    Halts δ c₀ ↔ ∃ n, orbit next s₀ n = none := by
  have reach : ∀ n s, orbit next s₀ n = some s → ∃ t c, n ≤ t ∧ steps δ t c₀ = some c ∧ Rel s c := by
    intro n
    induction n with
    | zero =>
      intro s h
      cases h
      obtain ⟨t, c, ht, hr⟩ := h₀
      exact ⟨t, c, Nat.zero_le _, ht, hr⟩
    | succ n ih =>
      intro s h
      simp only [orbit] at h
      cases e : orbit next s₀ n with
      | none => rw [e] at h; cases h
      | some s₁ =>
        rw [e] at h
        obtain ⟨t, c, ht, hc, hr⟩ := ih s₁ e
        have hs := hstep s₁ c hr
        simp only [Option.bind] at h
        rw [h] at hs
        obtain ⟨c', ⟨u, hu⟩, hr'⟩ := hs
        exact ⟨t + (u + 1), c', by omega, steps_seq δ hc hu, hr'⟩
  constructor
  · intro hb
    apply Classical.byContradiction
    intro hn
    have hall : ∀ n, ∃ s, orbit next s₀ n = some s := by
      intro n
      cases e : orbit next s₀ n with
      | none => exact absurd ⟨n, e⟩ hn
      | some s => exact ⟨s, rfl⟩
    apply not_halts_of_forall δ _ hb
    apply forall_of_unbounded δ (fun t => ∃ c, steps δ t c₀ = some c)
    · intro N
      obtain ⟨s, hs⟩ := hall N
      obtain ⟨t, c, ht, h, -⟩ := reach N s hs
      exact ⟨t, ht, c, h⟩
    · intro t ht
      exact ht
  · rintro ⟨n, h⟩
    induction n with
    | zero => cases h
    | succ n ih =>
      cases e : orbit next s₀ n with
      | none => exact ih e
      | some s =>
        simp only [orbit, e, Option.bind] at h
        obtain ⟨t, c, -, hc, hr⟩ := reach n s e
        have hs := hstep s c hr
        rw [h] at hs
        obtain ⟨u, d, hu, hd⟩ := hs
        exact ⟨t + u, d, steps_seq δ hc hu, hd⟩

end Orbit

/-! ## Runs of ones -/

theorem ones_cons (n : Nat) (s : Tape) : cons true (rep n [true] s) = rep (n + 1) [true] s := rfl

theorem ones_snoc (n : Nat) (s : Tape) : rep n [true] (cons true s) = rep (n + 1) [true] s :=
  rep_app_comm n [true] s

theorem ones_two (n : Nat) (s : Tape) : rep n [true, true] s = rep (2 * n) [true] s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep_succ, ih, show 2 * (n + 1) = 2 * n + 1 + 1 by omega]; rfl

theorem ones_three (n : Nat) (s : Tape) : rep n [true, true, true] s = rep (3 * n) [true] s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep_succ, ih, show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by omega]; rfl

theorem ones_ones (a b : Nat) (s : Tape) : rep a [true] (rep b [true] s) = rep (a + b) [true] s :=
  (rep_add a b [true] s).symm

theorem ones_one (s : Tape) : cons true s = rep 1 [true] s := rfl

theorem ones_eq {a b : Nat} (h : a = b) (s : Tape) : rep a [true] s = rep b [true] s := by rw [h]

/-- A repeat of `w` twice is a repeat of `w ++ w`. -/
theorem rep_double (n : Nat) (w : List Bool) (s : Tape) : rep (2 * n) w s = rep n (w ++ w) s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, rep_succ, rep_succ, ih, rep_succ, app_app]

theorem cfg_eq {Q : Type} {l l' r r' : Tape} {s : Q} (h₁ : l = l') (h₂ : r = r') :
    (⟨l, r, s⟩ : Cfg Q) = ⟨l', r', s⟩ := by subst h₁ h₂; rfl

theorem rep_congr {a b : Nat} {w : List Bool} {s s' : Tape} (h₁ : a = b) (h₂ : s = s') : rep a w s = rep b w s' := by
  subst h₁ h₂; rfl

theorem cons_congr {x : Bool} {s s' : Tape} (h : s = s') : cons x s = cons x s' := by subst h; rfl

/-- Close an equation of configurations whose tapes are the same words with counts equal by `omega`, without
unfolding the repeats (`rfl` on large counts can time out). -/
macro "tape_cong" : tactic => `(tactic| repeat' (first
  | with_reducible rfl
  | (simp only [rep_zero]; done)
  | refine cfg_eq ?_ ?_
  | refine rep_congr ?_ ?_
  | refine cons_congr ?_
  | omega))

/-! A normal form for `simp`: copies of a repeated word next to its repeat move to the far side of it, and a repeat
`(w)^(n+1)` is written `(w)^n w`, so that both sides of an equation of tapes become the same term. -/

theorem rep_succ_far (n : Nat) (w : List Bool) (s : Tape) : rep (n + 1) w s = rep n w (app w s) :=
  (rep_app_comm n w s).symm
theorem rep_near1 (n : Nat) (a : Bool) (s : Tape) : cons a (rep n [a] s) = rep n [a] (cons a s) :=
  rep_rotate n [a] [a] [a] rfl s
theorem rep_near2 (n : Nat) (a b : Bool) (s : Tape) :
    cons a (cons b (rep n [a, b] s)) = rep n [a, b] (cons a (cons b s)) := rep_rotate n [a, b] [a, b] [a, b] rfl s
theorem rep_near3 (n : Nat) (a b c : Bool) (s : Tape) :
    cons a (cons b (cons c (rep n [a, b, c] s))) = rep n [a, b, c] (cons a (cons b (cons c s))) :=
  rep_rotate n [a, b, c] [a, b, c] [a, b, c] rfl s
theorem rep_near4 (n : Nat) (a b c d : Bool) (s : Tape) :
    cons a (cons b (cons c (cons d (rep n [a, b, c, d] s)))) = rep n [a, b, c, d] (cons a (cons b (cons c (cons d s)))) :=
  rep_rotate n [a, b, c, d] [a, b, c, d] [a, b, c, d] rfl s
theorem rep_rot (n : Nat) (a b : Bool) (s : Tape) : cons a (rep n [b, a] s) = rep n [a, b] (cons a s) :=
  rep_rotate n [a] [b, a] [a, b] rfl s
theorem rep_rot3 (n : Nat) (a b c : Bool) (s : Tape) : cons a (rep n [b, c, a] s) = rep n [a, b, c] (cons a s) :=
  rep_rotate n [a] [b, c, a] [a, b, c] rfl s
theorem rep_rot4 (n : Nat) (a b c d : Bool) (s : Tape) :
    cons a (rep n [b, c, d, a] s) = rep n [a, b, c, d] (cons a s) :=
  rep_rotate n [a] [b, c, d, a] [a, b, c, d] rfl s
theorem rep_dbl (n : Nat) (a : Bool) (s : Tape) : rep n [a, a] s = rep (2 * n) [a] s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep_succ, ih, show 2 * (n + 1) = 2 * n + 1 + 1 by omega]; rfl
theorem rep_zeros1 (n : Nat) : rep n [false] blank = blank := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep_succ, ih]; exact cons_false_blank
theorem rep_zeros2 (n : Nat) : rep n [false, false] blank = blank := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep_succ, ih]; simp only [app_cons, app_nil, cons_false_blank]
theorem rep_rep (n m : Nat) (w : List Bool) (s : Tape) : rep n w (rep m w s) = rep (n + m) w s :=
  (rep_add n m w s).symm

/-- An equation of configurations that holds by unfolding, or after joining copies of a word to its repeats and
`0 0^∞ = 0^∞`, with counts equal by `omega`. -/
macro "cfg_rfl" : tactic => `(tactic| first
  | with_reducible rfl
  | (simp only [cons_false_blank]; done)
  | (simp only [cons_false_blank, rep_succ_far, rep_near1, rep_near2, rep_near3, rep_near4, rep_rot, rep_rot3, rep_rot4, rep_dbl, rep_zero,
      rep_zeros1, rep_zeros2, app_cons, app_nil]; done)
  | (simp only [cons_false_blank, rep_succ_far, rep_near1, rep_near2, rep_near3, rep_near4, rep_rot, rep_rot3, rep_rot4, rep_dbl, rep_rep,
      rep_zero, rep_zeros1, rep_zeros2, app_cons, app_nil]; tape_cong; done)
  | rfl)

end TM
