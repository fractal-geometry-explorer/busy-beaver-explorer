import Counter2
import Blank

/-! # The counter model of 1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---, and the reduction to it

A state `(n0, G)` stands for the counter configuration `ccfg n0 G` (`Counter.lean`).  `bounceM` is one bounce of
the machine, **defined on every state**.

First the state is read the way the borrow sees it (`norm`): the borrow passes the leading groups `(0, m+1)`; an
empty group `(0,0)` followed by a group `(1, n)` is one more `x` on the tape (`1 · 1 10 = 1110`), so the two join
the block before them; and `(0,0), (0,0), (1,n)` is the same tape as the group `(0, n+1)`.  These are equalities
of tapes (`norm_sound`).  What is left after the passed groups decides the bounce (`term`):

* a group `(e+1, n)`: a ternary decrement (`bounce_any`), followed by a merge if it leaves an empty group in
  front of a group with digit 1;
* nothing: the round ends (`exhaust`, `exhaust0`);
* empty groups `(0,0)` at the very end: `bounce_t1`, `bounce_t2`, `bounce_t3`;
* one or two empty groups and then a group with digit `e + 2`: the machine turns round there (`mid1`, `mid2`);
* an empty group followed by `(0, n+1)`, or by `(0,0), (0, n+1)`, or by two empty groups and anything more:
  the machine halts (`bounce_halt`).

`norm` leaves no other case (`norm_shape`), so `bounceM` never returns `stuck` (`bounceM_ne_stuck`), and
`bounceM_next` / `bounceM_halt` prove that the model is right: a `next` is a run of the machine of at least one
step, a `halt` a halting configuration. -/

namespace H40361

open TM

/-- The outcome of one bounce.  (`stuck` is never returned: `bounceM_ne_stuck`.) -/
inductive Res where
  | next (n0 : Nat) (G : List (Nat × Nat))
  | halt
  | stuck
  deriving DecidableEq, Repr

/-- Read the groups as the borrow sees them: `norm n0 racc G = (n0', ms, r)`, where `racc` is the list of the
groups already passed, reversed (a passed group `(0, m+1)` is recorded as `m`), `ms` the passed groups in order
and `r` the rest of the list, which starts with the group that stops the borrow. -/
def norm : Nat → List Nat → List (Nat × Nat) → Nat × List Nat × List (Nat × Nat)
  | n0, racc, (0, m + 1) :: G => norm n0 (m :: racc) G
  | n0, [], (0, 0) :: (1, n) :: G => norm (n0 + 1 + n) [] G
  | n0, m :: racc, (0, 0) :: (1, n) :: G => norm n0 ((m + 1 + n) :: racc) G
  | n0, racc, (0, 0) :: (0, 0) :: (1, n) :: G => norm n0 (n :: racc) G
  | n0, racc, G => (n0, racc.reverse, G)

/-- `(0,0), (0,0), (1,n)` is the same tape as `(0, n+1)`: `1 · 1 · 1 10 = 1 · 1110`. -/
theorem merge_two (n : Nat) (B : List (Nat × Nat)) (F : Tape) :
    grps ((0, 0) :: (0, 0) :: (1, n) :: B) F = grps ((0, n + 1) :: B) F := rfl

/-- `norm` does not change the tape. -/
theorem norm_sound (n0 : Nat) (racc : List Nat) (G : List (Nat × Nat)) (F : Tape) :
    ctape (norm n0 racc G).1 ((norm n0 racc G).2.1.map (fun m => (0, m + 1)) ++ (norm n0 racc G).2.2) F =
      ctape n0 (racc.reverse.map (fun m => (0, m + 1)) ++ G) F := by
  fun_induction norm n0 racc G with
  | case1 n0 racc m G ih =>
    rw [ih]; simp [List.map_append, List.append_assoc]
  | case2 n0 n G ih =>
    rw [ih]; simp only [List.reverse_nil, List.map_nil, List.nil_append]; rw [merge_first]
  | case3 n0 m racc n G ih =>
    rw [ih]
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.cons_append, List.nil_append]
    unfold ctape
    rw [merge_mid, show m + 1 + n + 1 = m + 1 + 1 + n by omega]
  | case4 n0 racc n G ih =>
    rw [ih]
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.cons_append, List.nil_append]
    unfold ctape
    rw [grps_append, grps_append, merge_two]
  | case5 n0 racc G _ _ _ _ => rfl

/-- What `norm` leaves starts with a group that stops the borrow. -/
theorem norm_shape (n0 : Nat) (racc : List Nat) (G : List (Nat × Nat)) :
    (∀ m G', (norm n0 racc G).2.2 ≠ (0, m + 1) :: G') ∧
    (∀ n G', (norm n0 racc G).2.2 ≠ (0, 0) :: (1, n) :: G') ∧
    (∀ n G', (norm n0 racc G).2.2 ≠ (0, 0) :: (0, 0) :: (1, n) :: G') := by
  fun_induction norm n0 racc G with
  | case1 n0 racc m G ih => exact ih
  | case2 n0 n G ih => exact ih
  | case3 n0 m racc n G ih => exact ih
  | case4 n0 racc n G ih => exact ih
  | case5 n0 racc G h1 h2 h3 h4 =>
    refine ⟨fun m G' e => h1 m G' e, fun n G' e => ?_, fun n G' e => h4 n G' e⟩
    cases racc with
    | nil => exact h2 n G' rfl e
    | cons m racc => exact h3 m racc n G' rfl e

/-- After a decrement: merge an empty group `(0,0)` with a following group `(1, n')` into the block before. -/
def afterDec (n0 : Nat) (ms : List Nat) (g : Nat × Nat) (rest : List (Nat × Nat)) : Nat × List (Nat × Nat) :=
  match g, rest with
  | (0, 0), (1, n') :: rest' =>
    match ms.reverse with
    | [] => (n0 + 1 + n', rest')
    | m :: rms => (n0, (rms.reverse.map (fun m => (2, m))) ++ (2, m + 1 + n') :: rest')
  | _, _ => (n0, ms.map (fun m => (2, m)) ++ g :: rest)

/-- The bounce, given the passed groups `ms` and the rest `r` of the list. -/
def term (n0 : Nat) (ms : List Nat) (r : List (Nat × Nat)) : Res :=
  match r with
  | [] =>
    match ms.reverse with
    | [] => .next 0 [(1, n0), (0, 0)]
    | k :: rinit => .next 0 ((1, n0 + 1) :: rinit.reverse.map (fun m => (0, m + 1)) ++ [(0, k), (0, 0)])
  | (e + 1, n) :: rest =>
    .next (afterDec (n0 + 1) ms (e, n) rest).1 (afterDec (n0 + 1) ms (e, n) rest).2
  | (0, _ + 1) :: _ => .stuck
  | (0, 0) :: rest =>
    match rest with
    | [] => .next (n0 + 1) (ms.map (fun m => (2, m)))
    | [(0, 0)] => .next (n0 + 1) (ms.map (fun m => (2, m)) ++ [(0, 0), (0, 0)])
    | [(0, 0), (0, 0)] => .next (n0 + 1) (ms.map (fun m => (2, m)) ++ [(1, 0)])
    | (0, _ + 1) :: _ => .halt
    | (1, _) :: _ => .stuck
    | (e + 2, n) :: rest' => .next 0 ((1, n0 + 1) :: ms.map (fun m => (0, m + 1)) ++ (0, 0) :: (e, n) :: rest')
    | (0, 0) :: (0, _ + 1) :: _ => .halt
    | (0, 0) :: (1, _) :: _ => .stuck
    | (0, 0) :: (e + 2, n) :: rest' =>
      .next 0 ((1, n0 + 1) :: ms.map (fun m => (0, m + 1)) ++ (0, 0) :: (0, 0) :: (e, n) :: rest')
    | (0, 0) :: (0, 0) :: (0, 0) :: _ => .halt
    | (0, 0) :: (0, 0) :: (0, _ + 1) :: _ => .halt
    | (0, 0) :: (0, 0) :: (_ + 1, _) :: _ => .halt

/-- One bounce of the counter. -/
def bounceM (n0 : Nat) (G : List (Nat × Nat)) : Res :=
  term (norm n0 [] G).1 (norm n0 [] G).2.1 (norm n0 [] G).2.2

theorem ccfg_parts (n0 : Nat) (G : List (Nat × Nat)) :
    ccfg n0 G = ccfg (norm n0 [] G).1 ((norm n0 [] G).2.1.map (fun m => (0, m + 1)) ++ (norm n0 [] G).2.2) := by
  unfold ccfg; rw [norm_sound]; rfl

theorem afterDec_sound (n0 : Nat) (ms : List Nat) (g : Nat × Nat) (rest : List (Nat × Nat)) :
    ccfg (afterDec n0 ms g rest).1 (afterDec n0 ms g rest).2 = ccfg n0 (ms.map (fun m => (2, m)) ++ g :: rest) := by
  unfold afterDec
  split
  · rename_i n' rest'
    split
    · rename_i h
      have : ms = [] := List.reverse_eq_nil_iff.mp h
      subst this
      unfold ccfg; simp only [List.map_nil, List.nil_append]
      rw [merge_first]
    · rename_i m rms h
      have : ms = rms.reverse ++ [m] := by
        rw [← List.reverse_reverse ms, h]; simp
      subst this
      unfold ccfg ctape
      simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
        List.nil_append]
      rw [merge_mid]
  · rfl

theorem term_next {n0 : Nat} {ms : List Nat} {r : List (Nat × Nat)} {n0' : Nat} {G' : List (Nat × Nat)}
    (h : term n0 ms r = .next n0' G') :
    ∃ t, 0 < t ∧ steps t (ccfg n0 (ms.map (fun m => (0, m + 1)) ++ r)) = some (ccfg n0' G') := by
  unfold term at h
  rcases r with _ | ⟨⟨d, n⟩, rest⟩
  · -- the end: exhaustion
    simp only at h
    split at h
    · rename_i hk
      have : ms = [] := List.reverse_eq_nil_iff.mp hk
      subst this
      injection h with h1 h2
      subst h1; subst h2
      exact exhaust0 n0
    · rename_i k rinit hk
      injection h with h1 h2
      subst h1; subst h2
      have : ms = rinit.reverse ++ [k] := by rw [← List.reverse_reverse ms, hk]; simp
      subst this
      simp only [List.append_nil]
      exact exhaust n0 rinit.reverse k
  · rcases d with _ | e
    · rcases n with _ | n
      · -- an empty group
        simp only at h
        split at h <;> (try cases h)
        · exact bounce_t1 n0 ms
        · exact bounce_t2 n0 ms
        · exact bounce_t3 n0 ms
        · exact mid1 n0 ms _ _ _ _
        · exact mid2 n0 ms _ _ _ _
      · simp only at h; cases h
    · -- a decrement
      simp only at h
      injection h with h1 h2; subst h1; subst h2
      rw [afterDec_sound]
      exact bounce_any (n0 := n0) (ms := ms) (e := e) (n := n) (rest := rest) (F := cons true blank)

theorem grps_head (A : List (Nat × Nat)) (Z : Tape) : ∃ Y, grps A (cons true Z) = cons true Y := by
  cases A with
  | nil => exact ⟨Z, rfl⟩
  | cons g A => exact ⟨_, rfl⟩

theorem term_halt {n0 : Nat} {ms : List Nat} {r : List (Nat × Nat)} (h : term n0 ms r = .halt) :
    Halts trans (ccfg n0 (ms.map (fun m => (0, m + 1)) ++ r)) := by
  unfold term at h
  rcases r with _ | ⟨⟨d, n⟩, rest⟩
  · simp only at h; split at h <;> cases h
  · rcases d with _ | e
    · rcases n with _ | n
      · simp only at h
        unfold ccfg
        have e0 : ∀ A : List (Nat × Nat), ctape n0 (ms.map (fun m => (0, m + 1)) ++ (0, 0) :: A) (cons true blank) =
            ctape n0 (ms.map (fun m => (0, m + 1))) (cons true (grps A (cons true blank))) := by
          intro A; unfold ctape; rw [grps_append]; rfl
        rw [e0]
        split at h <;> (try cases h) <;>
          (simp only [grps, grp, rep_succ, rep_zero, app_cons, app_nil]
           first
            | exact bounce_halt n0 ms _
            | (rename_i tl; obtain ⟨Y, hY⟩ := grps_head tl blank; rw [hY]; exact bounce_halt n0 ms _))
      · simp only at h; cases h
    · simp only at h; cases h

theorem term_ne_stuck (n0 : Nat) (ms : List Nat) (r : List (Nat × Nat))
    (h1 : ∀ m G', r ≠ (0, m + 1) :: G') (h2 : ∀ n G', r ≠ (0, 0) :: (1, n) :: G')
    (h3 : ∀ n G', r ≠ (0, 0) :: (0, 0) :: (1, n) :: G') : term n0 ms r ≠ .stuck := by
  intro h
  unfold term at h
  rcases r with _ | ⟨⟨d, n⟩, rest⟩
  · simp only at h; split at h <;> cases h
  · rcases d with _ | e
    · rcases n with _ | n
      · simp only at h
        split at h <;> (try cases h)
        · exact h2 _ _ rfl
        · exact h3 _ _ rfl
      · exact h1 _ _ rfl
    · simp only at h; cases h

/-- **The model is defined everywhere**: a bounce is never `stuck`. -/
theorem bounceM_ne_stuck (n0 : Nat) (G : List (Nat × Nat)) : bounceM n0 G ≠ .stuck := by
  obtain ⟨h1, h2, h3⟩ := norm_shape n0 [] G
  exact term_ne_stuck _ _ _ h1 h2 h3

/-- **The model is right (steps).**  A `next` of `bounceM` is reached by the machine in at least one step. -/
theorem bounceM_next {n0 : Nat} {G : List (Nat × Nat)} {n0' : Nat} {G' : List (Nat × Nat)}
    (h : bounceM n0 G = .next n0' G') : ∃ t, 0 < t ∧ steps t (ccfg n0 G) = some (ccfg n0' G') := by
  rw [ccfg_parts]; exact term_next h

/-- **The model is right (halting).**  A `halt` of `bounceM` is a halting configuration of the machine. -/
theorem bounceM_halt {n0 : Nat} {G : List (Nat × Nat)} (h : bounceM n0 G = .halt) :
    Halts trans (ccfg n0 G) := by
  rw [ccfg_parts]; exact term_halt h

theorem steps_add (a b : Nat) : ∀ c : Config,
    TM.steps trans (a + b) c = (TM.steps trans a c).bind (TM.steps trans b) := by
  induction a with
  | zero => intro c; simp [TM.steps]
  | succ a ih =>
    intro c
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [e]
    cases h : TM.step trans c with
    | none => simp [TM.steps, h]
    | some c' => simp [TM.steps, h, ih c']

/-- The run of the model: `k` bounces from a result. -/
def runM : Nat → Res → Res
  | 0, r => r
  | k + 1, .next n0 G => runM k (bounceM n0 G)
  | _ + 1, r => r

theorem runM_halt_stuck (k : Nat) : runM k .halt = .halt ∧ runM k .stuck = .stuck := by
  cases k <;> exact ⟨rfl, rfl⟩

theorem halts_of_steps {a : Nat} {c c' : Config} (h : steps a c = some c') (hc : Halts trans c') :
    Halts trans c := by
  obtain ⟨n, c'', h1, h2⟩ := hc
  exact ⟨a + n, c'', steps_seq trans h h1, h2⟩

/-- A `halt` of the model's run is a halt of the machine. -/
theorem halts_of_runM (k : Nat) : ∀ n0 G, runM k (.next n0 G) = .halt → Halts trans (ccfg n0 G) := by
  induction k with
  | zero => intro n0 G h; cases h
  | succ k ih =>
    intro n0 G h
    show Halts trans (ccfg n0 G)
    change runM k (bounceM n0 G) = .halt at h
    cases hb : bounceM n0 G with
    | next n0' G' =>
      rw [hb] at h
      obtain ⟨t, _, ht⟩ := bounceM_next hb
      exact halts_of_steps ht (ih n0' G' h)
    | halt => exact bounceM_halt hb
    | stuck => rw [hb, (runM_halt_stuck k).2] at h; cases h

/-- `k` bounces of the model are at least `k` steps of the machine. -/
theorem steps_of_runM (k : Nat) : ∀ n0 G n0' G', runM k (.next n0 G) = .next n0' G' →
    ∃ t, k ≤ t ∧ steps t (ccfg n0 G) = some (ccfg n0' G') := by
  induction k with
  | zero => intro n0 G n0' G' h; cases h; exact ⟨0, Nat.le_refl 0, rfl⟩
  | succ k ih =>
    intro n0 G n0' G' h
    change runM k (bounceM n0 G) = .next n0' G' at h
    cases hb : bounceM n0 G with
    | next n1 G1 =>
      rw [hb] at h
      obtain ⟨t, ht0, ht⟩ := bounceM_next hb
      obtain ⟨t', ht', h'⟩ := ih n1 G1 n0' G' h
      exact ⟨t + t', by omega, steps_seq trans ht h'⟩
    | halt => rw [hb, (runM_halt_stuck k).1] at h; cases h
    | stuck => rw [hb, (runM_halt_stuck k).2] at h; cases h

/-- The run of the model never gets stuck. -/
theorem runM_ne_stuck (k : Nat) : ∀ n0 G, runM k (.next n0 G) ≠ .stuck := by
  induction k with
  | zero => intro n0 G h; cases h
  | succ k ih =>
    intro n0 G h
    change runM k (bounceM n0 G) = .stuck at h
    cases hb : bounceM n0 G with
    | next n1 G1 => rw [hb] at h; exact ih n1 G1 h
    | halt => rw [hb, (runM_halt_stuck k).1] at h; cases h
    | stuck => exact bounceM_ne_stuck n0 G hb

/-- **Reduction.**  From any counter configuration, the machine halts exactly when the model's run reaches
`halt`. -/
theorem halts_iff_runM (n0 : Nat) (G : List (Nat × Nat)) :
    Halts trans (ccfg n0 G) ↔ ∃ k, runM k (.next n0 G) = .halt := by
  constructor
  · intro hh
    refine Classical.byContradiction fun hne => ?_
    have hn : ∀ k, ∃ n0' G', runM k (.next n0 G) = .next n0' G' := by
      intro k
      cases e : runM k (.next n0 G) with
      | next a b => exact ⟨a, b, rfl⟩
      | halt => exact absurd ⟨k, e⟩ hne
      | stuck => exact absurd e (runM_ne_stuck k n0 G)
    apply not_halts_of_forall trans _ hh
    apply forall_of_unbounded trans (fun m => ∃ c', steps m (ccfg n0 G) = some c')
    · intro n
      obtain ⟨a, b, e⟩ := hn n
      obtain ⟨t, ht, h⟩ := steps_of_runM n n0 G a b e
      exact ⟨t, ht, _, h⟩
    · intro m hm; exact hm
  · rintro ⟨k, hk⟩
    exact halts_of_runM k n0 G hk

/-- From blank tape the machine reaches the counter `(0; (1,5), (0,0))` in 403 steps. -/
theorem blank_to_counter : steps 403 init = some (ccfg 0 [(1, 5), (0, 0)]) := by
  have h : fsteps 403 (FCfg.blank .A) = some ⟨[], [false, true, false, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true], .C⟩ := by decide +kernel
  exact blank_reaches trans h

/-- **The machine halts from blank tape iff the counter model, started at `(0; (1,5), (0,0))`, reaches `halt`.**
No hypothesis: the model is defined on every state (`bounceM_ne_stuck`). -/
theorem halts_iff_model :
    HaltsFromBlank ↔ ∃ k, runM k (.next 0 [(1, 5), (0, 0)]) = .halt := by
  rw [← halts_iff_runM 0 _]
  constructor
  · rintro ⟨n, c, h1, h2⟩
    -- no halt in the first 10,000 steps, so the halt comes after the counter configuration at step 403
    have hn : 403 ≤ n := by
      refine Classical.byContradiction fun hlt => ?_
      obtain ⟨c', hc'⟩ := blank_runs_kernel
      have e : 10000 = n + ((10000 - n - 1) + 1) := by omega
      change TM.steps trans 10000 init = _ at hc'
      rw [e, steps_halt trans h1 h2] at hc'
      cases hc'
    obtain ⟨d, rfl⟩ : ∃ d, n = 403 + d := ⟨n - 403, by omega⟩
    have hb : TM.steps trans 403 init = some (ccfg 0 [(1, 5), (0, 0)]) := blank_to_counter
    rw [steps_add, hb] at h1
    exact ⟨d, c, h1, h2⟩
  · intro h; exact halts_of_steps blank_to_counter h

end H40361
