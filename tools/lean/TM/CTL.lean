import TM.Basic

/-!
# Closed tape languages

A regular invariant of a machine's runs, checked by evaluation.  Each side of the head is read outward from the head
(nearest cell first) by a finite automaton with numbered states, a list of edges `(q, x, q')` and a list of states
that accept the blank tape.  `Lang M q t` says the automaton accepts the stream `t` from `q`: either `t` is blank and
`q` accepts blank, or `t` is `x` in front of a stream accepted from some `q'` with an edge `(q, x, q')`.

A set `S` of abstract configurations `(state, left automaton state, right automaton state)` stands for the
configurations `Inv` whose streams the two automata accept from those states.  `check` is a computation, so `decide`
can run it: the start `⟨blank, blank, q₀⟩` is in the set, and every non-halting step from the set lands in it again.
Then (`reach`) every configuration of the run from `q₀` is in the set.  If the set allows no halt (`noHalt`), the
machine never halts (`not_halts`); if every halt it allows has a right state in a list `B` of states accepting only
blank tape (`haltsBlank`, `blankOnly`), every halt has only blank cells after the head (`halt_tail_blank`), so the
machine can halt only at the right edge of what it has written.  `no_double_zero` is the same kind of consequence for
two 0s in a row to the right of the head.

`tools/py/bbtools/ctl.py` finds the automata and the set (from windows of a few cells) and runs the same check.
-/

namespace TM.CTL

/-- A finite automaton on a stream, nearest cell first. -/
structure Auto where
  edges : List (Nat × Bool × Nat)
  acc : List Nat

/-- The streams the automaton accepts from a state. -/
inductive Lang (M : Auto) : Nat → Tape → Prop
  | blank {q : Nat} : q ∈ M.acc → Lang M q TM.blank
  | cons {q q' : Nat} {x : Bool} {t : Tape} : (q, x, q') ∈ M.edges → Lang M q' t → Lang M q (TM.cons x t)

/-- The ways an accepted stream can start: its first cell and the state that accepts the rest. -/
def Auto.pops (M : Auto) (q : Nat) : List (Bool × Nat) :=
  (M.edges.filter (fun e => e.1 == q)).map (fun e => e.2) ++ (if q ∈ M.acc then [(false, q)] else [])

theorem cons_head_tail (t : Tape) : TM.cons (t 0) (tail t) = t := by
  funext n; cases n <;> rfl

theorem Lang.pop {M : Auto} {q : Nat} {t : Tape} (h : Lang M q t) :
    ∃ p ∈ M.pops q, t 0 = p.1 ∧ Lang M p.2 (tail t) := by
  cases h with
  | blank hq => exact ⟨(false, q), by simp [Auto.pops, hq], rfl, by rw [tail_blank]; exact Lang.blank hq⟩
  | @cons _ q' x t he ht =>
    refine ⟨(x, q'), ?_, rfl, ht⟩
    simp only [Auto.pops, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq]
    exact Or.inl ⟨_, ⟨he, rfl⟩, rfl⟩

/-- The states accepting only the blank tape: no edge on 1, and edges on 0 lead back into the list. -/
def blankOnly (M : Auto) (B : List Nat) : Bool :=
  M.edges.all (fun e => !(decide (e.1 ∈ B)) || (e.2.1 == false && decide (e.2.2 ∈ B)))

theorem Lang.blank_of_blankOnly {M : Auto} {B : List Nat} (hB : blankOnly M B = true) {q : Nat} {t : Tape}
    (h : Lang M q t) (hq : q ∈ B) : t = TM.blank := by
  induction h with
  | blank _ => rfl
  | @cons q q' x t he _ ih =>
    simp only [blankOnly, List.all_eq_true] at hB
    have := hB _ he
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at this
    rcases this with h1 | ⟨hx, hq'⟩
    · exact absurd hq h1
    · subst hx; rw [ih hq']; exact cons_false_blank

variable {Q : Type} [DecidableEq Q]

/-- The configurations an abstract set stands for. -/
def Inv (ML MR : Auto) (S : List (Q × Nat × Nat)) (c : Cfg Q) : Prop :=
  ∃ ql qr, (c.st, ql, qr) ∈ S ∧ Lang ML ql c.l ∧ Lang MR qr c.r

/-- A right move writing `w` lands in the set: some state reaching `ql` on `w` takes the new left stream. -/
def okR (ML : Auto) (S : List (Q × Nat × Nat)) (s' : Q) (w : Bool) (ql qr' : Nat) : Bool :=
  ML.edges.any (fun e => e.2.1 == w && e.2.2 == ql && decide ((s', e.1, qr') ∈ S))

/-- A left move writing `w` over the cell `y` lands in the set: states reading `y` then `w` reach `qr'`. -/
def okL (MR : Auto) (S : List (Q × Nat × Nat)) (s' : Q) (y w : Bool) (ql' qr' : Nat) : Bool :=
  MR.edges.any (fun e1 => e1.2.1 == w && e1.2.2 == qr' &&
    MR.edges.any (fun e0 => e0.2.1 == y && e0.2.2 == e1.1 && decide ((s', ql', e0.1) ∈ S)))

section
variable (δ : Q → Bool → Option (Bool × Dir × Q))

/-- The closure test: from each abstract configuration, each head symbol and each non-halting transition. -/
def closed (ML MR : Auto) (S : List (Q × Nat × Nat)) : Bool :=
  S.all (fun a => (MR.pops a.2.2).all (fun p =>
    match δ a.1 p.1 with
    | none => true
    | some (w, .R, s') => okR ML S s' w a.2.1 p.2
    | some (w, .L, s') => (ML.pops a.2.1).all (fun y => okL MR S s' y.1 w y.2 p.2)))

/-- The start `⟨blank, blank, q₀⟩` is in the set. -/
def starts (ML MR : Auto) (S : List (Q × Nat × Nat)) (q₀ : Q) : Bool :=
  S.any (fun a => decide (a.1 = q₀) && decide (a.2.1 ∈ ML.acc) && decide (a.2.2 ∈ MR.acc))

theorem inv_step {ML MR : Auto} {S : List (Q × Nat × Nat)} (hS : closed δ ML MR S = true) {c c' : Cfg Q}
    (hc : Inv ML MR S c) (hs : step δ c = some c') : Inv ML MR S c' := by
  obtain ⟨ql, qr, hmem, hl, hr⟩ := hc
  obtain ⟨⟨x, qr'⟩, hp, hx, hr'⟩ := hr.pop
  simp only [closed, List.all_eq_true] at hS
  have h1 := hS _ hmem _ hp
  simp only at hx hr' h1
  unfold step at hs
  rw [hx] at hs
  cases hδ : δ c.st x with
  | none => rw [hδ] at hs; cases hs
  | some t =>
    obtain ⟨w, d, s'⟩ := t
    rw [hδ] at hs h1
    cases d with
    | R =>
      simp only [Option.some.injEq] at hs
      subst hs
      simp only [okR, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
      obtain ⟨⟨p, w', q⟩, he, ⟨hw, hq⟩, hm⟩ := h1
      simp only at hw hq hm
      subst hw hq
      exact ⟨p, qr', hm, Lang.cons he hl, hr'⟩
    | L =>
      simp only [Option.some.injEq] at hs
      subst hs
      obtain ⟨⟨y, ql'⟩, hy, hy0, hl'⟩ := hl.pop
      simp only [List.all_eq_true] at h1
      have h2 := h1 _ hy
      simp only [okL, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
      obtain ⟨⟨p1, w', q1⟩, he1, ⟨hw, hq1⟩, ⟨p0, y', q0⟩, he0, ⟨hy', hq0⟩, hm⟩ := h2
      simp only at hw hq1 hy' hq0 hm hy0
      subst hw hq1 hy' hq0
      refine ⟨ql', p0, hm, hl', ?_⟩
      rw [hy0]
      exact Lang.cons he0 (Lang.cons he1 hr')

theorem inv_steps {ML MR : Auto} {S : List (Q × Nat × Nat)} (hS : closed δ ML MR S = true) :
    ∀ (n : Nat) {c c' : Cfg Q}, Inv ML MR S c → steps δ n c = some c' → Inv ML MR S c'
  | 0, c, c', hc, h => by simp [steps] at h; exact h ▸ hc
  | n + 1, c, c', hc, h => by
    cases hs : step δ c with
    | none => simp [steps, hs] at h
    | some d =>
      rw [steps_succ_of_step δ n hs] at h
      exact inv_steps hS n (inv_step δ hS hc hs) h

/-- Every configuration of the run from `q₀` is in the set. -/
theorem reach {ML MR : Auto} {S : List (Q × Nat × Nat)} {q₀ : Q} (hS : closed δ ML MR S = true)
    (h₀ : starts ML MR S q₀ = true) {n : Nat} {c : Cfg Q} (h : steps δ n (blankCfg q₀) = some c) :
    Inv ML MR S c := by
  refine inv_steps δ hS n ?_ h
  simp only [starts, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h₀
  obtain ⟨⟨s, ql, qr⟩, hm, ⟨hs, hl⟩, hr⟩ := h₀
  simp only at hs hl hr
  subst hs
  exact ⟨ql, qr, hm, Lang.blank hl, Lang.blank hr⟩

/-- Every halt the set allows leaves only blank cells after the head: the abstract configurations where a halting
transition can fire have, after the head symbol, a right state in `B`. -/
def haltsBlank (MR : Auto) (S : List (Q × Nat × Nat)) (B : List Nat) : Bool :=
  S.all (fun a => (MR.pops a.2.2).all (fun p => (δ a.1 p.1).isSome || decide (p.2 ∈ B)))

omit [DecidableEq Q] in
theorem halt_tail_blank {ML MR : Auto} {S : List (Q × Nat × Nat)} {B : List Nat} (hB : blankOnly MR B = true)
    (hH : haltsBlank δ MR S B = true) {c : Cfg Q} (hc : Inv ML MR S c) (hs : step δ c = none) :
    tail c.r = TM.blank := by
  obtain ⟨ql, qr, hmem, _, hr⟩ := hc
  obtain ⟨⟨x, qr'⟩, hp, hx, hr'⟩ := hr.pop
  simp only [haltsBlank, List.all_eq_true] at hH
  have h1 := hH _ hmem _ hp
  simp only at hx hr' h1
  unfold step at hs
  rw [hx] at hs
  cases hδ : δ c.st x with
  | none =>
    rw [hδ] at h1
    simp only [Option.isSome_none, Bool.false_or, decide_eq_true_eq] at h1
    exact hr'.blank_of_blankOnly hB h1
  | some t =>
    rw [hδ] at hs
    obtain ⟨w, d, s'⟩ := t
    cases d <;> cases hs

/-- The set allows no halt at all. -/
def noHalt (MR : Auto) (S : List (Q × Nat × Nat)) : Bool :=
  S.all (fun a => (MR.pops a.2.2).all (fun p => (δ a.1 p.1).isSome))

/-- A closed set that allows no halt proves that the machine never halts from `q₀`. -/
theorem not_halts {ML MR : Auto} {S : List (Q × Nat × Nat)} {q₀ : Q} (hS : closed δ ML MR S = true)
    (h₀ : starts ML MR S q₀ = true) (hN : noHalt δ MR S = true) : ¬ Halts δ (blankCfg q₀) := by
  rintro ⟨n, c, h, hs⟩
  obtain ⟨ql, qr, hmem, _, hr⟩ := reach δ hS h₀ h
  obtain ⟨⟨x, qr'⟩, hp, hx, _⟩ := hr.pop
  simp only [noHalt, List.all_eq_true] at hN
  have h1 := hN _ hmem _ hp
  simp only at hx h1
  unfold step at hs
  rw [hx] at hs
  cases hδ : δ c.st x with
  | none => rw [hδ] at h1; cases h1
  | some t =>
    rw [hδ] at hs
    obtain ⟨w, d, s'⟩ := t
    cases d <;> cases hs

/-- The states the automaton can be in after reading the word `w` from `q`. -/
def Auto.after (M : Auto) (q : Nat) : List Bool → List Nat
  | [] => [q]
  | x :: w => (M.pops q).flatMap (fun p => if p.1 == x then M.after p.2 w else [])

theorem Lang.after {M : Auto} : ∀ (w : List Bool) {q : Nat} {t : Tape}, Lang M q (app w t) →
    ∃ q' ∈ M.after q w, Lang M q' t
  | [], q, t, h => ⟨q, by simp [Auto.after], h⟩
  | x :: w, q, t, h => by
    obtain ⟨⟨y, q1⟩, hp, hy, h1⟩ := h.pop
    simp only [app_cons, cons_zero, tail_cons] at hy h1
    obtain ⟨q', hq', h'⟩ := Lang.after w h1
    refine ⟨q', ?_, h'⟩
    simp only [Auto.after, List.mem_flatMap]
    exact ⟨(y, q1), hp, by simp [← hy, hq']⟩

/-- Two 0s in a row after the head lie in the blank region: `Rt` holds the right automaton's states for the
streams after the head cell (each head symbol leads into it, and it is closed under edges), and from each of them two
0s lead only to states in `B`. -/
def noDoubleZero (MR : Auto) (S : List (Q × Nat × Nat)) (Rt B : List Nat) : Bool :=
  S.all (fun a => (MR.pops a.2.2).all (fun p => decide (p.2 ∈ Rt))) &&
  Rt.all (fun q => (MR.pops q).all (fun p => decide (p.2 ∈ Rt)) &&
    (MR.after q [false, false]).all (fun q' => decide (q' ∈ B)))

omit [DecidableEq Q] in
theorem Lang.zero_zero {M : Auto} {B Rt : List Nat} (hB : blankOnly M B = true)
    (hR : ∀ q ∈ Rt, (∀ p ∈ M.pops q, p.2 ∈ Rt) ∧ ∀ q' ∈ M.after q [false, false], q' ∈ B) :
    ∀ (i : Nat) {q : Nat} {t : Tape}, q ∈ Rt → Lang M q t → t i = false → t (i + 1) = false →
      ∀ j, i ≤ j → t j = false
  | 0, q, t, hq, h, h0, h1, j, _ => by
    have e : t = app [false, false] (tail (tail t)) := by
      funext n; rcases n with _ | _ | n
      · exact h0
      · exact h1
      · rfl
    rw [e] at h
    obtain ⟨q', hq', h'⟩ := h.after [false, false]
    have := h'.blank_of_blankOnly hB ((hR q hq).2 q' hq')
    rw [e, this]
    rcases j with _ | _ | j <;> rfl
  | i + 1, q, t, hq, h, h0, h1, j, hj => by
    obtain ⟨p, hp, _, h'⟩ := h.pop
    have := Lang.zero_zero hB hR i ((hR q hq).1 p hp) h' h0 h1 (j - 1) (by omega)
    simpa [tail, show j - 1 + 1 = j by omega] using this

omit [DecidableEq Q] in
/-- In every configuration of the set, past the head cell, two 0s in a row are followed only by 0s. -/
theorem no_double_zero {ML MR : Auto} {S : List (Q × Nat × Nat)} {Rt B : List Nat} (hB : blankOnly MR B = true)
    (hZ : noDoubleZero MR S Rt B = true) {c : Cfg Q} (hc : Inv ML MR S c) {i : Nat}
    (h0 : c.r (i + 1) = false) (h1 : c.r (i + 2) = false) : ∀ j, i + 1 ≤ j → c.r j = false := by
  obtain ⟨ql, qr, hmem, _, hr⟩ := hc
  obtain ⟨p, hp, _, h'⟩ := hr.pop
  simp only [noDoubleZero, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hZ
  intro j hj
  have := Lang.zero_zero hB (fun q hq => hZ.2 q hq) i (hZ.1 _ hmem p hp) h' h0 h1 (j - 1) (by omega)
  simpa [tail, show j - 1 + 1 = j by omega] using this

end

end TM.CTL
