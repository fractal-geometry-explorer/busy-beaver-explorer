import TM

/-!
# Runs around one long repeated block

A tape `left-zone  m^k  right-zone` with `k` copies of a short word `m` in the middle and finitely many written
cells on each side.  The head works inside one zone cell by cell, and crosses the whole block at once by a shift
rule (`TM.cross_r` / `TM.cross_l`), which changes the word `m` but not `k`.  The simulator `astep` below never looks
at `k`: whatever it computes holds for every `k` (`arun_sound`, `arun_halt`).  It answers `stuck` when the head
reaches the block in a way no rule in its tables covers.

Generic in the machine `δ`; the rule tables are parameters, each rule proved by `rfl` in the machine's own file.
-/

namespace TM
namespace Zone

variable {Q : Type} [DecidableEq Q]

/-- A shift rule: state `q`, the word `u` that travels with the head, the block word `w` before and `v` after,
and the number of steps `s` per copy. -/
structure Rule (Q : Type) where
  q : Q
  u : List Bool
  w : List Bool
  v : List Bool
  s : Nat

inductive Side where
  | L | R
  deriving DecidableEq, Repr

/-- The head is in zone `z`; `a` the cells of that zone left of the head (nearest first), `b` the cells from the
head on; `m` the block word (read away from the head's zone); `o` the other zone (read away from the block). -/
structure ACfg (Q : Type) where
  z : Side
  a : List Bool
  b : List Bool
  m : List Bool
  o : List Bool
  st : Q
  deriving DecidableEq, Repr

inductive Res (α : Type) where
  | next (c : α)
  | halt
  | stuck
  deriving DecidableEq, Repr

/-- The configuration with `k` copies of the block. -/
def enc (k : Nat) (c : ACfg Q) : Cfg Q :=
  match c.z with
  | .L => ⟨app c.a blank, app c.b (rep k c.m (app c.o blank)), c.st⟩
  | .R => ⟨app c.a (rep k c.m (app c.o blank)), app c.b blank, c.st⟩

/-- `strip u l = some t` when `l = u ++ t`. -/
def strip : List Bool → List Bool → Option (List Bool)
  | [], l => some l
  | _ :: _, [] => none
  | x :: u, y :: l => if x = y then strip u l else none

theorem strip_spec : ∀ (u l t : List Bool), strip u l = some t → l = u ++ t
  | [], l, t, h => by simp [strip] at h; simp [h]
  | _ :: _, [], t, h => by simp [strip] at h
  | x :: u, y :: l, t, h => by
    simp only [strip] at h
    split at h
    · next e => subst e; simp [strip_spec u l t h]
    · cases h

/-- The first rule for state `q` and block word `m` whose `u` is a prefix of `ctx`, with the rest of `ctx`. -/
def find : List (Rule Q) → Q → List Bool → List Bool → Option (Rule Q × List Bool)
  | [], _, _, _ => none
  | r :: rs, q, m, ctx =>
    if r.q = q ∧ r.w = m then
      match strip r.u ctx with
      | some t => some (r, t)
      | none => find rs q m ctx
    else find rs q m ctx

theorem find_spec : ∀ (rs : List (Rule Q)) (q : Q) (m ctx : List Bool) (r : Rule Q) (t : List Bool),
    find rs q m ctx = some (r, t) → r ∈ rs ∧ r.q = q ∧ r.w = m ∧ ctx = r.u ++ t
  | [], _, _, _, _, _, h => by simp [find] at h
  | r' :: rs, q, m, ctx, r, t, h => by
    simp only [find] at h
    split at h
    · next hc =>
      split at h
      · next t' ht =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨List.mem_cons_self, hc.1, hc.2, strip_spec _ _ _ ht⟩
      · obtain ⟨h1, h2⟩ := find_spec rs q m ctx r t h
        exact ⟨List.mem_cons_of_mem _ h1, h2⟩
    · obtain ⟨h1, h2⟩ := find_spec rs q m ctx r t h
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

section
variable (δ : Q → Bool → Option (Bool × Dir × Q))

/-- `L u q> w^k R` becomes `L v^k u q> R`. -/
def RuleR (r : Rule Q) : Prop :=
  ∀ L R : Tape, steps δ r.s ⟨app r.u L, app r.w R, r.q⟩ = some ⟨app r.u (app r.v L), R, r.q⟩

/-- `L w^k q> u R` becomes `L q> u v^k R`. -/
def RuleL (r : Rule Q) : Prop :=
  ∀ L R : Tape, steps δ r.s ⟨app r.w L, app r.u R, r.q⟩ = some ⟨L, app r.u (app r.v R), r.q⟩

variable (rr rl : List (Rule Q))

/-- An ordinary step in the right zone. -/
def plainR (q : Q) (a b m o : List Bool) : Res (ACfg Q) :=
  match δ q (b.headD false) with
  | none => .halt
  | some (w, .R, q') => .next ⟨.R, w :: a, b.tail, m, o, q'⟩
  | some (w, .L, q') =>
    match a with
    | [] => .stuck
    | x :: a' => .next ⟨.R, a', x :: w :: b.tail, m, o, q'⟩

/-- One move of the simulator: a machine step inside a zone, or a whole crossing of the block. -/
def astep (c : ACfg Q) : Res (ACfg Q) :=
  match c.z with
  | .L =>
    match c.b with
    | [] =>
      match find rr c.st c.m c.a with
      | some (r, t) => .next ⟨.R, r.u, c.o, r.v, t, c.st⟩
      | none => .stuck
    | x :: b' =>
      match δ c.st x with
      | none => .halt
      | some (w, .R, q') => .next ⟨.L, w :: c.a, b', c.m, c.o, q'⟩
      | some (w, .L, q') => .next ⟨.L, c.a.tail, c.a.headD false :: w :: b', c.m, c.o, q'⟩
  | .R =>
    match c.a with
    | [] =>
      match find rl c.st c.m c.b with
      | some (r, t) => .next ⟨.L, c.o, r.u, r.v, t, c.st⟩
      | none => plainR δ c.st [] c.b c.m c.o
    | x :: a' => plainR δ c.st (x :: a') c.b c.m c.o

/-- Moves until `stop` holds, at most `fuel` of them. -/
def arun (stop : ACfg Q → Bool) : Nat → ACfg Q → Res (ACfg Q)
  | 0, _ => .stuck
  | f + 1, c =>
    match astep δ rr rl c with
    | .next c' => if stop c' then .next c' else arun stop f c'
    | .halt => .halt
    | .stuck => .stuck

variable {δ rr rl}

omit [DecidableEq Q] in
theorem plainR_sound {q : Q} {a b m o : List Bool} {c' : ACfg Q} (k : Nat)
    (h : plainR δ q a b m o = .next c') :
    steps δ 1 ⟨app a (rep k m (app o blank)), app b blank, q⟩ = some (enc k c') := by
  unfold plainR at h
  have hd : app b blank 0 = b.headD false := app_head b
  cases e : δ q (b.headD false) with
  | none => rw [e] at h; cases h
  | some t =>
    obtain ⟨w, d, q'⟩ := t
    rw [e] at h
    cases d with
    | R =>
      simp only [Res.next.injEq] at h
      subst h
      simp only [steps, step, hd, e, enc, app_cons, app_tail]
    | L =>
      cases a with
      | nil => simp at h
      | cons x a' =>
        simp only [Res.next.injEq] at h
        subst h
        simp only [steps, step, hd, e, enc, app_cons, app_tail]
        rfl

omit [DecidableEq Q] in
theorem plainR_halt {q : Q} {a b m o : List Bool} (k : Nat) (h : plainR δ q a b m o = .halt) :
    step δ ⟨app a (rep k m (app o blank)), app b blank, q⟩ = none := by
  unfold plainR at h
  have hd : app b blank 0 = b.headD false := app_head b
  cases e : δ q (b.headD false) with
  | none => simp only [step, hd, e]
  | some t =>
    obtain ⟨w, d, q'⟩ := t
    rw [e] at h
    cases d with
    | R => cases h
    | L => cases a <;> simp at h

theorem astep_sound (hR : ∀ r ∈ rr, RuleR δ r) (hL : ∀ r ∈ rl, RuleL δ r) (k : Nat) {c c' : ACfg Q}
    (h : astep δ rr rl c = .next c') : ∃ n, steps δ n (enc k c) = some (enc k c') := by
  obtain ⟨z, a, b, m, o, q⟩ := c
  cases z with
  | L =>
    cases b with
    | nil =>
      simp only [astep] at h
      cases e : find rr q m a with
      | none => rw [e] at h; cases h
      | some p =>
        obtain ⟨r, t⟩ := p
        rw [e] at h
        simp only [Res.next.injEq] at h
        subst h
        obtain ⟨hm, rfl, rfl, rfl⟩ := find_spec _ _ _ _ _ _ e
        refine ⟨k * r.s, ?_⟩
        have := cross_r δ (hR r hm) k (app t blank) (app o blank)
        simpa only [enc, app_nil, app_app] using this
    | cons x b' =>
      simp only [astep] at h
      refine ⟨1, ?_⟩
      cases e : δ q x with
      | none => rw [e] at h; cases h
      | some t =>
        obtain ⟨w, d, q'⟩ := t
        rw [e] at h
        cases d with
        | R =>
          simp only [Res.next.injEq] at h
          subst h
          simp only [steps, step, enc, app_cons, cons_zero, e, tail_cons]
        | L =>
          simp only [Res.next.injEq] at h
          subst h
          simp only [steps, step, enc, app_cons, cons_zero, e, tail_cons, app_tail, app_head]
  | R =>
    cases a with
    | nil =>
      simp only [astep] at h
      cases e : find rl q m b with
      | none =>
        rw [e] at h
        exact ⟨1, plainR_sound k h⟩
      | some p =>
        obtain ⟨r, t⟩ := p
        rw [e] at h
        simp only [Res.next.injEq] at h
        subst h
        obtain ⟨hm, rfl, rfl, rfl⟩ := find_spec _ _ _ _ _ _ e
        refine ⟨k * r.s, ?_⟩
        have := cross_l δ (hL r hm) k (app o blank) (app t blank)
        simpa only [enc, app_nil, app_app] using this
    | cons x a' =>
      simp only [astep] at h
      exact ⟨1, plainR_sound k h⟩

theorem astep_halt (k : Nat) {c : ACfg Q} (h : astep δ rr rl c = .halt) : step δ (enc k c) = none := by
  obtain ⟨z, a, b, m, o, q⟩ := c
  cases z with
  | L =>
    cases b with
    | nil =>
      simp only [astep] at h
      cases e : find rr q m a with
      | none => rw [e] at h; cases h
      | some p => rw [e] at h; cases h
    | cons x b' =>
      simp only [astep] at h
      cases e : δ q x with
      | none => simp only [step, enc, app_cons, cons_zero, e]
      | some t =>
        obtain ⟨w, d, q'⟩ := t
        rw [e] at h
        cases d <;> cases h
  | R =>
    cases a with
    | nil =>
      simp only [astep] at h
      cases e : find rl q m b with
      | none => rw [e] at h; exact plainR_halt k h
      | some p => rw [e] at h; cases h
    | cons x a' =>
      simp only [astep] at h
      exact plainR_halt k h

/-- A run of the simulator that ends at `c'` is a run of the machine, for every number `k` of copies. -/
theorem arun_sound (hR : ∀ r ∈ rr, RuleR δ r) (hL : ∀ r ∈ rl, RuleL δ r) (k : Nat) (stop : ACfg Q → Bool) :
    ∀ (f : Nat) (c c' : ACfg Q), arun δ rr rl stop f c = .next c' →
      stop c' = true ∧ ∃ n, steps δ n (enc k c) = some (enc k c') := by
  intro f
  induction f with
  | zero => intro c c' h; cases h
  | succ f ih =>
    intro c c' h
    simp only [arun] at h
    cases e : astep δ rr rl c with
    | halt => rw [e] at h; cases h
    | stuck => rw [e] at h; cases h
    | next d =>
      rw [e] at h
      obtain ⟨n1, h1⟩ := astep_sound hR hL k e
      by_cases hs : stop d = true
      · simp only [hs, ite_true, Res.next.injEq] at h
        subst h
        exact ⟨hs, n1, h1⟩
      · simp only [hs] at h
        obtain ⟨hs', n2, h2⟩ := ih d c' h
        exact ⟨hs', _, steps_seq δ h1 h2⟩

/-- A run of the simulator that halts is a halting run of the machine, for every `k`. -/
theorem arun_halt (hR : ∀ r ∈ rr, RuleR δ r) (hL : ∀ r ∈ rl, RuleL δ r) (k : Nat) (stop : ACfg Q → Bool) :
    ∀ (f : Nat) (c : ACfg Q), arun δ rr rl stop f c = .halt → Halts δ (enc k c) := by
  intro f
  induction f with
  | zero => intro c h; cases h
  | succ f ih =>
    intro c h
    simp only [arun] at h
    cases e : astep δ rr rl c with
    | halt => exact ⟨0, _, rfl, astep_halt k e⟩
    | stuck => rw [e] at h; cases h
    | next d =>
      rw [e] at h
      obtain ⟨n1, h1⟩ := astep_sound hR hL k e
      by_cases hs : stop d = true
      · simp only [hs, ite_true] at h; cases h
      · simp only [hs] at h
        obtain ⟨n2, c2, h2, h3⟩ := ih d h
        exact ⟨_, c2, steps_seq δ h1 h2, h3⟩

end

end Zone
end TM
