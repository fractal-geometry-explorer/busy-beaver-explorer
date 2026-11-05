import BB6.Marks

/-!
# The machine's conserved count, mod 3

The number of 1s on the tape, plus 2 for state B and 1 for states C, D, E and F, never changes mod 3: every transition
that writes a 1 over a 0 moves to a state of weight one less, every one that writes a 0 over a 1 to a state of weight
one more, and the others keep the weight (the lab notes, "They pass the machine's conserved count", October 24, found it
by search and found no other conserved count of this kind).  It is 0 on the blank tape in state A.

Read off a round start it fixes the width mod 3: a round start with three walls reached from blank tape has
W ≡ 2 (mod 6), and a one-marker clean tape W ≡ 4 (mod 6) (`blank_pass_mod6`, `blank_clean_mod6`).  The trees of the
end-to-end theorems work with 2-adic classes, which hold every residue mod 3, so they cannot see this.

The tape streams are infinite, so the count is taken over the first `N` cells of each stream (`ones`) for an `N` past
which both streams are blank (`Supp`); a step moves that bound by at most one.
-/

namespace BB6

/-- The number of 1s among the first `n` cells of a stream. -/
def ones : Nat → Tape → Nat
  | 0, _ => 0
  | n + 1, s => (if s 0 then 1 else 0) + ones n (tail s)

/-- Every cell from `N` on is 0. -/
def Supp (s : Tape) (N : Nat) : Prop := ∀ n, N ≤ n → s n = false

/-- The weight of a state in the count. -/
def wt : St → Nat
  | .A => 0
  | .B => 2
  | _ => 1

/-- The count of a configuration over the first `N` cells of each stream. -/
def charge (c : Cfg) (N : Nat) : Nat := ones N c.l + ones N c.r + wt c.st

@[simp] theorem ones_zero (s : Tape) : ones 0 s = 0 := rfl

theorem ones_succ (n : Nat) (s : Tape) : ones (n + 1) s = (if s 0 then 1 else 0) + ones n (tail s) := rfl

theorem ones_cons (n : Nat) (a : Bool) (s : Tape) : ones (n + 1) (cons a s) = (if a then 1 else 0) + ones n s := rfl

theorem supp_tail {s : Tape} {N : Nat} (h : Supp s (N + 1)) : Supp (tail s) N :=
  fun n hn => h (n + 1) (by omega)

theorem supp_tail' {s : Tape} {N : Nat} (h : Supp s N) : Supp (tail s) N :=
  fun n hn => h (n + 1) (by omega)

theorem supp_cons {s : Tape} {N : Nat} (a : Bool) (h : Supp s N) : Supp (cons a s) (N + 1) := by
  intro n hn
  match n, hn with
  | n + 1, hn => exact h n (by omega)

theorem supp_mono {s : Tape} {N M : Nat} (h : Supp s N) (hNM : N ≤ M) : Supp s M :=
  fun n hn => h n (by omega)

theorem supp_blank (N : Nat) : Supp blank N := fun _ _ => rfl

theorem ones_of_supp0 {s : Tape} (h : Supp s 0) : ∀ M, ones M s = 0 := by
  intro M
  induction M generalizing s with
  | zero => rfl
  | succ M ih =>
    rw [ones_succ, h 0 (Nat.le_refl 0), ih (supp_tail' h)]
    rfl

/-- Past the support the count does not change. -/
theorem ones_stable {s : Tape} {N : Nat} (h : Supp s N) : ∀ M, N ≤ M → ones M s = ones N s := by
  induction N generalizing s with
  | zero => intro M _; rw [ones_of_supp0 h M, ones_of_supp0 h 0]
  | succ N ih =>
    intro M hM
    match M, hM with
    | M + 1, hM => rw [ones_succ, ones_succ, ih (supp_tail h) M (by omega)]

theorem ones_blank (M : Nat) : ones M blank = 0 := ones_of_supp0 (supp_blank 0) M

/-- One step keeps the count mod 3 and moves the support by at most one cell. -/
theorem step_charge {c c' : Cfg} (h : step c = some c') {N : Nat} (hN : 1 ≤ N) (hl : Supp c.l N) (hr : Supp c.r N) :
    Supp c'.l (N + 1) ∧ Supp c'.r (N + 1) ∧ charge c' (N + 1) % 3 = charge c N % 3 := by
  obtain ⟨l, r, st⟩ := c
  simp only at hl hr
  -- the counts around the head
  have hl1 : ones N l = (if l 0 then 1 else 0) + ones N (tail l) := by
    rw [← ones_succ, ones_stable hl (N + 1) (by omega)]
  have hr1 : ones N r = (if r 0 then 1 else 0) + ones N (tail r) := by
    rw [← ones_succ, ones_stable hr (N + 1) (by omega)]
  have htl : ones (N + 1) (tail l) = ones N (tail l) := ones_stable (supp_tail' hl) (N + 1) (by omega)
  have htr : ones (N + 1) (tail r) = ones N (tail r) := ones_stable (supp_tail' hr) (N + 1) (by omega)
  -- the two shapes of a step
  have hR : ∀ (w : Bool) (s : St), c' = ⟨cons w l, tail r, s⟩ →
      Supp c'.l (N + 1) ∧ Supp c'.r (N + 1) ∧
        charge c' (N + 1) = (if w then 1 else 0) + ones N l + ones N (tail r) + wt s := by
    intro w s e
    subst e
    refine ⟨supp_cons w hl, supp_mono (supp_tail' hr) (by omega), ?_⟩
    show ones (N + 1) (cons w l) + ones (N + 1) (tail r) + wt s = _
    rw [ones_cons, htr]
  have hL : ∀ (w : Bool) (s : St), c' = ⟨tail l, cons (l 0) (cons w (tail r)), s⟩ →
      Supp c'.l (N + 1) ∧ Supp c'.r (N + 1) ∧
        charge c' (N + 1) = ones N (tail l) + (if l 0 then 1 else 0) + (if w then 1 else 0) + ones N (tail r) + wt s := by
    intro w s e
    subst e
    have hs : Supp (cons (l 0) (cons w (tail r))) (N + 1) := by
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      exact supp_cons _ (supp_cons _ (supp_tail hr))
    refine ⟨supp_mono (supp_tail' hl) (by omega), hs, ?_⟩
    show ones (N + 1) (tail l) + ones (N + 1) (cons (l 0) (cons w (tail r))) + wt s = _
    rw [htl, ← ones_stable hs (N + 2) (by omega), ones_cons, ones_cons]
    omega
  have hc : charge ⟨l, r, st⟩ N = ones N l + ones N r + wt st := rfl
  cases st <;> cases h0 : r 0 <;> simp [step, trans, h0] at h
  all_goals first
    | (obtain ⟨h1, h2, h3⟩ := hR _ _ h.symm
       refine ⟨h1, h2, ?_⟩
       rw [h3, hc, hr1, h0]
       simp [wt] <;> omega)
    | (obtain ⟨h1, h2, h3⟩ := hL _ _ h.symm
       refine ⟨h1, h2, ?_⟩
       rw [h3, hc, hr1, hl1, h0]
       simp [wt] <;> omega)

/-- So does every run. -/
theorem steps_charge : ∀ (n : Nat) {c c' : Cfg} {N : Nat}, steps n c = some c' → 1 ≤ N → Supp c.l N → Supp c.r N →
    Supp c'.l (N + n) ∧ Supp c'.r (N + n) ∧ charge c' (N + n) % 3 = charge c N % 3
  | 0, c, c', N, h, _, hl, hr => by
    simp [steps] at h
    subst h
    exact ⟨hl, hr, rfl⟩
  | n + 1, c, c', N, h, hN, hl, hr => by
    cases hs : step c with
    | none => simp [steps, hs] at h
    | some d =>
      rw [steps_succ_of_step n hs] at h
      obtain ⟨hl', hr', hc'⟩ := step_charge hs hN hl hr
      obtain ⟨h1, h2, h3⟩ := steps_charge n h (by omega) hl' hr'
      have e : N + 1 + n = N + (n + 1) := by omega
      rw [e] at h1 h2 h3
      exact ⟨h1, h2, by rw [h3, hc']⟩

/-- From blank tape the count is 0 mod 3 at every step, over any bound past the support. -/
theorem blank_charge {k : Nat} {c : Cfg} (h : steps k ⟨blank, blank, .A⟩ = some c) :
    ∃ N, Supp c.l N ∧ Supp c.r N ∧ charge c N % 3 = 0 := by
  obtain ⟨h1, h2, h3⟩ := steps_charge k h (N := 1) (Nat.le_refl 1) (supp_blank 1) (supp_blank 1)
  refine ⟨1 + k, h1, h2, ?_⟩
  rw [h3]
  simp [charge, ones_blank, wt]

/-! ## The count at a round start -/

/-- The 1s of a stripe. -/
def stripeOnes (b : Bool) (n : Nat) : Nat := if b then (n + 1) / 2 else n / 2

theorem ones_stripe (b : Bool) (n M : Nat) (s : Tape) :
    ones (n + M) (stripe b n s) = stripeOnes b n + ones M s := by
  induction n generalizing b with
  | zero => simp [stripeOnes]
  | succ n ih =>
    have e : n + 1 + M = (n + M) + 1 := by omega
    rw [e, stripe_succ, ones_cons, ih]
    cases b <;> simp [stripeOnes] <;> omega

theorem supp_stripe (b : Bool) (n : Nat) {s : Tape} {M : Nat} (h : Supp s M) : Supp (stripe b n s) (n + M) := by
  induction n generalizing b with
  | zero => simpa using h
  | succ n ih =>
    have e : n + 1 + M = (n + M) + 1 := by omega
    rw [e, stripe_succ]
    exact supp_cons _ (ih _)

theorem ones_app2 (a b : Bool) (M : Nat) (s : Tape) :
    ones (M + 2) (app [a, b] s) = (if a then 1 else 0) + (if b then 1 else 0) + ones M s := by
  simp only [app_cons, app_nil]
  rw [ones_cons, ones_cons]
  omega

theorem supp_app2 (a b : Bool) {s : Tape} {M : Nat} (h : Supp s M) : Supp (app [a, b] s) (M + 2) := by
  simp only [app_cons, app_nil]
  exact supp_cons _ (supp_cons _ h)

/-- The left stream of a round start: one 1 (the leftmost 1 of the tape). -/
theorem roundStart_left (ms : List Mark) (W : Nat) :
    Supp (roundStart ms W).l 3 ∧ ones 3 (roundStart ms W).l = 1 := by
  refine ⟨supp_cons _ (supp_cons _ (supp_cons _ (supp_blank 0))), ?_⟩
  show ones 3 (cons false (cons false (cons true blank))) = 1
  rw [ones_cons, ones_cons, ones_cons, ones_blank]
  rfl

/-- **A round start with three walls**: its count is 2 plus the 1s of the four stripes. -/
theorem roundStart3_charge {a b c W : Nat} (h1 : 4 ≤ a) (h2 : a + 2 ≤ b) (h3 : b + 2 ≤ c) (h4 : c + 2 ≤ W) :
    Supp (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] W).l W ∧ Supp (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] W).r W ∧
      charge (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] W) W =
        2 + (a - 3) / 2 + (b - a - 1) / 2 + (c - b - 1) / 2 + (W - c - 1) / 2 := by
  obtain ⟨hlS, hl1⟩ := roundStart_left [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] W
  -- the right stream, mark by mark
  have e4 : W - (c + 2) + 0 = W - (c + 2) := by omega
  have s4 : Supp (build false (c + 2) [] W) (W - (c + 2)) := by
    show Supp (stripe (!false) (W - (c + 2)) blank) _
    exact supp_stripe _ (W - (c + 2)) (supp_blank 0)
  have o4 : ones (W - (c + 2)) (build false (c + 2) [] W) = stripeOnes true (W - (c + 2)) := by
    show ones (W - (c + 2)) (stripe (!false) (W - (c + 2)) blank) = _
    have := ones_stripe true (W - (c + 2)) 0 blank
    rw [ones_blank, Nat.add_zero, Nat.add_zero] at this
    exact this
  have s3 : Supp (build false (b + 2) [⟨.W, c⟩] W) ((c - (b + 2)) + ((W - (c + 2)) + 2)) :=
    supp_stripe true _ (supp_app2 false false s4)
  have o3 : ones ((c - (b + 2)) + ((W - (c + 2)) + 2)) (build false (b + 2) [⟨.W, c⟩] W) =
      stripeOnes true (c - (b + 2)) + stripeOnes true (W - (c + 2)) := by
    show ones _ (stripe true (c - (b + 2)) (app [false, false] (build false (c + 2) [] W))) = _
    rw [ones_stripe, ones_app2, o4]; simp
  have s2 : Supp (build false (a + 2) [⟨.W, b⟩, ⟨.W, c⟩] W)
      ((b - (a + 2)) + (((c - (b + 2)) + ((W - (c + 2)) + 2)) + 2)) :=
    supp_stripe true _ (supp_app2 false false s3)
  have o2 : ones ((b - (a + 2)) + (((c - (b + 2)) + ((W - (c + 2)) + 2)) + 2))
      (build false (a + 2) [⟨.W, b⟩, ⟨.W, c⟩] W) =
      stripeOnes true (b - (a + 2)) + stripeOnes true (c - (b + 2)) + stripeOnes true (W - (c + 2)) := by
    show ones _ (stripe true (b - (a + 2)) (app [false, false] (build false (b + 2) [⟨.W, c⟩] W))) = _
    rw [ones_stripe, ones_app2, o3]; simp; omega
  have s1 : Supp (build false 4 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] W)
      ((a - 4) + (((b - (a + 2)) + (((c - (b + 2)) + ((W - (c + 2)) + 2)) + 2)) + 2)) :=
    supp_stripe true _ (supp_app2 false false s2)
  have o1 : ones ((a - 4) + (((b - (a + 2)) + (((c - (b + 2)) + ((W - (c + 2)) + 2)) + 2)) + 2))
      (build false 4 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] W) =
      stripeOnes true (a - 4) + stripeOnes true (b - (a + 2)) + stripeOnes true (c - (b + 2)) +
        stripeOnes true (W - (c + 2)) := by
    show ones _ (stripe true (a - 4) (app [false, false] (build false (a + 2) [⟨.W, b⟩, ⟨.W, c⟩] W))) = _
    rw [ones_stripe, ones_app2, o2]; simp; omega
  have eW : (a - 4) + (((b - (a + 2)) + (((c - (b + 2)) + ((W - (c + 2)) + 2)) + 2)) + 2) = W - 4 := by omega
  rw [eW] at s1 o1
  have hrS : Supp (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] W).r (W - 3) := by
    have := supp_cons false s1
    have e : W - 4 + 1 = W - 3 := by omega
    rw [e] at this; exact this
  have hr1 : ones (W - 3) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] W).r = ones (W - 4) (build false 4 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] W) := by
    have e : W - 3 = (W - 4) + 1 := by omega
    show ones (W - 3) (cons false _) = _
    rw [e, ones_cons]; simp
  refine ⟨supp_mono hlS (by omega), supp_mono hrS (by omega), ?_⟩
  simp only [charge]
  rw [ones_stable hlS W (by omega), hl1, ones_stable hrS W (by omega), hr1, o1]
  simp [stripeOnes, wt, roundStart]
  omega

/-- **A one-marker clean tape**: its count is 4 plus the 1s of the stripe before the end marker. -/
theorem roundStart_clean_charge {W : Nat} (hW : 6 ≤ W) :
    Supp (roundStart [⟨.M, W - 2⟩] W).l W ∧ Supp (roundStart [⟨.M, W - 2⟩] W).r W ∧
      charge (roundStart [⟨.M, W - 2⟩] W) W = 4 + (W - 5) / 2 := by
  obtain ⟨hlS, hl1⟩ := roundStart_left [⟨.M, W - 2⟩] W
  have s0 : Supp (build true W [] W) 0 := by
    show Supp (stripe false (W - W) blank) 0
    rw [Nat.sub_self]; exact supp_blank 0
  have s1 : Supp (build false 4 [⟨.M, W - 2⟩] W) ((W - 2 - 4) + (0 + 2)) := by
    show Supp (stripe true (W - 2 - 4) (app [true, true] (build true (W - 2 + 2) [] W))) _
    have e : W - 2 + 2 = W := by omega
    rw [e]; exact supp_stripe true _ (supp_app2 true true s0)
  have o1 : ones ((W - 2 - 4) + (0 + 2)) (build false 4 [⟨.M, W - 2⟩] W) = stripeOnes true (W - 2 - 4) + 2 := by
    show ones _ (stripe true (W - 2 - 4) (app [true, true] (build true (W - 2 + 2) [] W))) = _
    have e : W - 2 + 2 = W := by omega
    rw [e, ones_stripe, ones_app2, ones_of_supp0 s0]; simp
  have eW : (W - 2 - 4) + (0 + 2) = W - 4 := by omega
  rw [eW] at s1 o1
  have hrS : Supp (roundStart [⟨.M, W - 2⟩] W).r (W - 3) := by
    have := supp_cons false s1
    have e : W - 4 + 1 = W - 3 := by omega
    rw [e] at this; exact this
  have hr1 : ones (W - 3) (roundStart [⟨.M, W - 2⟩] W).r = ones (W - 4) (build false 4 [⟨.M, W - 2⟩] W) := by
    have e : W - 3 = (W - 4) + 1 := by omega
    show ones (W - 3) (cons false _) = _
    rw [e, ones_cons]; simp
  refine ⟨supp_mono hlS (by omega), supp_mono hrS (by omega), ?_⟩
  simp only [charge]
  rw [ones_stable hlS W (by omega), hl1, ones_stable hrS W (by omega), hr1, o1]
  simp [stripeOnes, wt, roundStart]
  omega

/-- The count of a configuration reached from blank tape is 0 mod 3 over every bound past its support. -/
theorem blank_charge_at {k : Nat} {c : Cfg} (h : steps k ⟨blank, blank, .A⟩ = some c) {N : Nat}
    (hl : Supp c.l N) (hr : Supp c.r N) : charge c N % 3 = 0 := by
  obtain ⟨M, hlM, hrM, hM⟩ := blank_charge h
  have e : charge c N = charge c (max N M) := by
    simp only [charge]
    rw [ones_stable hl (max N M) (Nat.le_max_left _ _), ones_stable hr (max N M) (Nat.le_max_left _ _)]
  have e' : charge c M = charge c (max N M) := by
    simp only [charge]
    rw [ones_stable hlM (max N M) (Nat.le_max_right _ _), ones_stable hrM (max N M) (Nat.le_max_right _ _)]
  rw [e, ← e', hM]

/-- **A round start with three walls reached from blank tape**, with the parities of a pass start (first wall odd,
second even, third odd, width even), **has W ≡ 2 (mod 6).** -/
theorem blank_pass_mod6 {k a b c W : Nat} (h : steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] W))
    (h1 : 4 ≤ a) (h2 : a + 2 ≤ b) (h3 : b + 2 ≤ c) (h4 : c + 2 ≤ W)
    (pa : a % 2 = 1) (pb : b % 2 = 0) (pc : c % 2 = 1) (pW : W % 2 = 0) : W % 6 = 2 := by
  obtain ⟨hl, hr, hc⟩ := roundStart3_charge h1 h2 h3 h4
  have := blank_charge_at h hl hr
  rw [hc] at this
  omega

/-- **A one-marker clean tape reached from blank tape**, of even width, **has W ≡ 4 (mod 6).** -/
theorem blank_clean_mod6 {k W : Nat} (h : steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W))
    (hW : 6 ≤ W) (pW : W % 2 = 0) : W % 6 = 4 := by
  obtain ⟨hl, hr, hc⟩ := roundStart_clean_charge hW
  have := blank_charge_at h hl hr
  rw [hc] at this
  omega

#print axioms blank_pass_mod6
#print axioms blank_clean_mod6

end BB6
