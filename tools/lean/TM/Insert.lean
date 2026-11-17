import TM.Basic

/-!
# Two runs that differ by one inserted word

`c'` is `c` with a finite word `v` inserted somewhere on the tape.  While the head of `c` stays on its own cells,
the two runs make the same steps.  When the head of `c` crosses the place of the insertion, the head of `c'` meets
`v`; if the machine, run on `v` alone from that side and in that state, comes out at the other side of `v` in the
same state (a *transparent crossing*, `zsim`), the relation holds again with the new contents of `v`.  If not, the
insertion may be moved one cell further away from the head when the cell behind it equals the first cell of `v`
(`x v = v' x` with `v'` the rotation of `v`, a *shift*).  Otherwise the run reaches a *bad* moment, where this
relation cannot follow it.

`tnext` computes the next position and contents of the insertion from `c` alone, `trk` follows the run of `c`, and
`Good t c` says that the followed run never reaches a bad moment.  The main result:

* `halts_iff_of_good`: if `Rel t c c'` and `Good t c`, then `c` halts if and only if `c'` halts.

`Good` is a statement about every length of the run, so it is the hypothesis that a separate argument has to
supply; `trk` lets a program check it on a finite part of the run.  Kernel only (axioms `propext`,
`Classical.choice`, `Quot.sound`; no `native_decide`).
-/

set_option linter.unusedSectionVars false

namespace TM

variable {Q : Type} [DecidableEq Q] (δ : Q → Bool → Option (Bool × Dir × Q))

/-! ## The machine on a finite word -/

/-- The end of a run on a finite word: the head left it at the right end (cells of the word left of the head,
nearest first) or at the left end (cells right of the head, in order), in a state, after a number of steps. -/
inductive ZR (Q : Type) where
  | right (lw : List Bool) (s : Q) (k : Nat)
  | left (rw : List Bool) (s : Q) (k : Nat)

def ZR.addk {Q : Type} (a : Nat) : ZR Q → ZR Q
  | .right lw s k => .right lw s (k + a)
  | .left rw s k => .left rw s (k + a)

/-- Run the machine on a finite word, head on the first cell of `rw`, `lw` the cells to its left (nearest first),
until the head leaves the word; `none` if it halts or the fuel runs out. -/
def zsim : Nat → List Bool → List Bool → Q → Option (ZR Q)
  | _, lw, [], s => some (.right lw s 0)
  | 0, _, _ :: _, _ => none
  | f + 1, lw, a :: rw, s =>
    match δ s a with
    | none => none
    | some (w, .R, s') => (zsim f (w :: lw) rw s').map (ZR.addk 1)
    | some (w, .L, s') =>
      match lw with
      | [] => some (.left (w :: rw) s' 1)
      | b :: lw' => (zsim f lw' (b :: w :: rw) s').map (ZR.addk 1)

theorem cons_head_tail (s : Tape) : cons (s 0) (tail s) = s := by
  funext n; cases n <;> rfl

theorem steps_one {c d : Cfg Q} (h : step δ c = some d) : steps δ 1 c = some d := by
  simp [steps, h]

theorem steps_succ' {k : Nat} {c d e : Cfg Q} (h : step δ c = some d) (h2 : steps δ k d = some e) :
    steps δ (k + 1) c = some e := by
  have := steps_seq δ (steps_one δ h) h2
  rw [Nat.add_comm]; exact this

/-- What a run on a finite word does on the whole tape. -/
theorem zsim_sound : ∀ (f : Nat) (lw rw : List Bool) (s : Q) (z : ZR Q), zsim δ f lw rw s = some z →
    ∀ L R : Tape, match z with
      | .right lw' s' k => steps δ k ⟨app lw L, app rw R, s⟩ = some ⟨app lw' L, R, s'⟩
      | .left rw' s' k => steps δ k ⟨app lw L, app rw R, s⟩ = some ⟨tail L, cons (L 0) (app rw' R), s'⟩ := by
  intro f
  induction f with
  | zero =>
    intro lw rw s z h L R
    cases rw with
    | nil => simp [zsim] at h; subst h; rfl
    | cons a rw => simp [zsim] at h
  | succ f ih =>
    intro lw rw s z h L R
    cases rw with
    | nil => simp [zsim] at h; subst h; rfl
    | cons a rw =>
      simp only [zsim] at h
      rcases hd : δ s a with _ | ⟨w, d, s'⟩
      · rw [hd] at h; cases h
      · rw [hd] at h
        cases d with
        | R =>
          simp only at h
          rcases hz : zsim δ f (w :: lw) rw s' with _ | z'
          · rw [hz] at h; cases h
          · rw [hz] at h
            simp only [Option.map_some, Option.some.injEq] at h
            subst h
            have hs : step δ ⟨app lw L, app (a :: rw) R, s⟩ = some ⟨app (w :: lw) L, app rw R, s'⟩ := by
              simp [step, hd]
            have := ih (w :: lw) rw s' z' hz L R
            cases z' with
            | right lw' s'' k => exact steps_succ' δ hs this
            | left rw' s'' k => exact steps_succ' δ hs this
        | L =>
          simp only at h
          cases lw with
          | nil =>
            simp only [Option.some.injEq] at h
            subst h
            show steps δ 1 _ = _
            apply steps_one
            simp [step, hd]
          | cons b lw' =>
            simp only at h
            rcases hz : zsim δ f lw' (b :: w :: rw) s' with _ | z'
            · rw [hz] at h; cases h
            · rw [hz] at h
              simp only [Option.map_some, Option.some.injEq] at h
              subst h
              have hs : step δ ⟨app (b :: lw') L, app (a :: rw) R, s⟩ =
                  some ⟨app lw' L, app (b :: w :: rw) R, s'⟩ := by
                simp [step, hd]
              have := ih lw' (b :: w :: rw) s' z' hz L R
              cases z' with
              | right lw' s'' k => exact steps_succ' δ hs this
              | left rw' s'' k => exact steps_succ' δ hs this

/-! ## The relation and its tracker -/

/-- Where the inserted word is: on the right of the head after `n ≥ 1` cells of the shared tape (`v` read left to
right), or on its left after `n` shared cells (`v` read right to left, nearest first). -/
structure Ins where
  right : Bool
  n : Nat
  v : List Bool

/-- `c'` is `c` with the word inserted as `t` says. -/
def Rel (t : Ins) (c c' : Cfg Q) : Prop :=
  c.st = c'.st ∧
    match t.right with
    | true => c.l = c'.l ∧ 1 ≤ t.n ∧ ∃ u X, u.length = t.n ∧ c.r = app u X ∧ c'.r = app u (app t.v X)
    | false => c.r = c'.r ∧ ∃ u X, u.length = t.n ∧ c.l = app u X ∧ c'.l = app u (app t.v X)

/-- One left rotation. -/
def rotL : List Bool → List Bool
  | [] => []
  | a :: v => v ++ [a]

/-- The next position and contents of the insertion after one step of `c`, or `none` at a bad moment (also when
`c` halts, where nothing is needed). -/
def tnext (fuel : Nat) (t : Ins) (c : Cfg Q) : Option Ins :=
  match δ c.st (c.r 0) with
  | none => none
  | some (w, d, s) =>
    if t.right then
      match d with
      | .L => some ⟨true, t.n + 1, t.v⟩
      | .R =>
        if 2 ≤ t.n then some ⟨true, t.n - 1, t.v⟩
        else
          match zsim δ fuel [] t.v s with
          | some (.right lw s' _) => if s' = s then some ⟨false, 0, lw⟩ else
              if t.v.head? = some (c.r 1) then some ⟨true, 1, rotL t.v⟩ else none
          | _ => if t.v.head? = some (c.r 1) then some ⟨true, 1, rotL t.v⟩ else none
    else
      match d with
      | .R => some ⟨false, t.n + 1, t.v⟩
      | .L =>
        if 1 ≤ t.n then some ⟨false, t.n - 1, t.v⟩
        else
          match t.v with
          | [] => some ⟨true, 1, []⟩
          | a :: vt =>
            match zsim δ fuel vt [a] s with
            | some (.left rw s' _) => if s' = s then some ⟨true, 1, rw⟩ else
                if a = c.l 0 then some ⟨false, 0, rotL (a :: vt)⟩ else none
            | _ => if a = c.l 0 then some ⟨false, 0, rotL (a :: vt)⟩ else none

theorem app_rotL (a : Bool) (v : List Bool) (X : Tape) : app (a :: v) (cons a X) = cons a (app (rotL (a :: v)) X) := by
  show cons a (app v (cons a X)) = cons a (app (v ++ [a]) X)
  rw [← app_app]; rfl

theorem app_length_cons {u : List Bool} {X : Tape} (h : 1 ≤ u.length) :
    ∃ a u', u = a :: u' ∧ app u X = cons a (app u' X) := by
  cases u with
  | nil => simp at h
  | cons a u' => exact ⟨a, u', rfl, rfl⟩

theorem relR {n : Nat} {v : List Bool} {c c' : Cfg Q} (hs : c.st = c'.st) (hl : c.l = c'.l) (hn : 1 ≤ n)
    (u : List Bool) (X : Tape) (hu : u.length = n) (h1 : c.r = app u X) (h2 : c'.r = app u (app v X)) :
    Rel ⟨true, n, v⟩ c c' := ⟨hs, hl, hn, u, X, hu, h1, h2⟩

theorem relL {n : Nat} {v : List Bool} {c c' : Cfg Q} (hs : c.st = c'.st) (hr : c.r = c'.r)
    (u : List Bool) (X : Tape) (hu : u.length = n) (h1 : c.l = app u X) (h2 : c'.l = app u (app v X)) :
    Rel ⟨false, n, v⟩ c c' := ⟨hs, hr, u, X, hu, h1, h2⟩

/-- One step of `c` that is not bad is matched by at least one step of `c'`. -/
theorem rel_step {fuel : Nat} {t t' : Ins} {c c' d : Cfg Q} (hr : Rel t c c') (hs : step δ c = some d)
    (ht : tnext δ fuel t c = some t') : ∃ k d', steps δ (k + 1) c' = some d' ∧ Rel t' d d' := by
  obtain ⟨l, r, q⟩ := c
  obtain ⟨l', r', q'⟩ := c'
  obtain ⟨hq, hrest⟩ := hr
  simp only at hq; subst hq
  rcases hd : δ q (r 0) with _ | ⟨w, dir, s⟩
  · simp [step, hd] at hs
  obtain ⟨tr, tn, tv⟩ := t
  cases tr with
  | true =>
    obtain ⟨hl, hn, u, X, hu, hrX, hr'X⟩ := hrest
    simp only at hl hn hu hrX hr'X; subst hl
    obtain ⟨a, u', rfl, -⟩ := app_length_cons (X := X) (show 1 ≤ u.length by omega)
    have h0 : r 0 = a := by rw [hrX]; rfl
    have h0' : r' 0 = a := by rw [hr'X]; rfl
    have hq0 : δ q (r' 0) = some (w, dir, s) := by rw [h0', ← h0]; exact hd
    cases dir with
    | L =>
      simp [tnext, hd] at ht; subst ht
      simp [step, hd] at hs; subst hs
      refine ⟨0, ⟨tail l, cons (l 0) (cons w (tail r')), s⟩, ?_, ?_⟩
      · apply steps_one; simp [step, hq0]
      · refine relR rfl rfl (by omega) (l 0 :: w :: u') X (by simp at hu ⊢; omega) ?_ ?_
        · show cons (l 0) (cons w (tail r)) = _; rw [hrX]; rfl
        · show cons (l 0) (cons w (tail r')) = _; rw [hr'X]; rfl
    | R =>
      simp [step, hd] at hs; subst hs
      have hstep' : step δ ⟨l, r', q⟩ = some ⟨cons w l, tail r', s⟩ := by simp [step, hq0]
      by_cases h2 : 2 ≤ tn
      · simp [tnext, hd, h2] at ht; subst ht
        refine ⟨0, _, steps_one δ hstep', ?_⟩
        obtain ⟨b, u'', rfl, -⟩ := app_length_cons (X := X) (show 1 ≤ u'.length by simp at hu; omega)
        refine relR rfl rfl (by simp at hu; omega) (b :: u'') X (by simp at hu ⊢; omega) ?_ ?_
        · show tail r = _; rw [hrX]; rfl
        · show tail r' = _; rw [hr'X]; rfl
      · have htn : tn = 1 := by omega
        subst htn
        have hu' : u' = [] := by simpa using hu
        subst hu'
        have hrX1 : r = cons a X := hrX
        have hr'X1 : r' = cons a (app tv X) := hr'X
        have shift : tv.head? = some (r 1) → t' = ⟨true, 1, rotL tv⟩ →
            ∃ k d', steps δ (k + 1) ⟨l, r', q⟩ = some d' ∧ Rel t' ⟨cons w l, tail r, s⟩ d' := by
          intro hh ht'
          subst ht'
          cases tv with
          | nil => simp at hh
          | cons b vt =>
            simp at hh
            have hX : X = cons b (tail X) := by
              have : r 1 = X 0 := by rw [hrX1]; rfl
              rw [hh, this]; exact (cons_head_tail X).symm
            refine ⟨0, _, steps_one δ hstep', ?_⟩
            refine relR rfl rfl (Nat.le_refl 1) [b] (tail X) rfl ?_ ?_
            · show tail r = cons b (tail X); rw [hrX1]; exact hX
            · show tail r' = cons b (app (rotL (b :: vt)) (tail X))
              rw [hr'X1, ← app_rotL, ← hX]; rfl
        simp only [tnext, hd, show ¬ 2 ≤ 1 by omega] at ht
        rcases hz : zsim δ fuel [] tv s with _ | z
        · rw [hz] at ht
          by_cases hh : tv.head? = some (r 1)
          · simp [hh] at ht; exact shift hh ht.symm
          · simp [hh] at ht
        · rw [hz] at ht
          cases z with
          | left rw s' k =>
            by_cases hh : tv.head? = some (r 1)
            · simp [hh] at ht; exact shift hh ht.symm
            · simp [hh] at ht
          | right lw s' k =>
            by_cases hs' : s' = s
            · subst hs'
              simp at ht; subst ht
              have hc := zsim_sound δ fuel [] tv s' _ hz (cons w l) X
              simp only [app_nil] at hc
              refine ⟨k, ⟨app lw (cons w l), X, s'⟩, ?_, ?_⟩
              · have : tail r' = app tv X := by rw [hr'X1]; rfl
                rw [this] at hstep'
                exact steps_succ' δ hstep' hc
              · refine relL rfl ?_ [] (cons w l) rfl rfl rfl
                show tail r = X; rw [hrX1]; rfl
            · simp only [hs', ite_false] at ht
              by_cases hh : tv.head? = some (r 1)
              · simp [hh] at ht; exact shift hh ht.symm
              · simp [hh] at ht
  | false =>
    obtain ⟨hrr, u, X, hu, hlX, hl'X⟩ := hrest
    simp only at hrr hu hlX hl'X; subst hrr
    cases dir with
    | R =>
      simp [tnext, hd] at ht; subst ht
      simp [step, hd] at hs; subst hs
      refine ⟨0, ⟨cons w l', tail r, s⟩, ?_, ?_⟩
      · apply steps_one; simp [step, hd]
      · refine relL rfl rfl (w :: u) X (by simp [hu]) ?_ ?_
        · show cons w l = _; rw [hlX]; rfl
        · show cons w l' = _; rw [hl'X]; rfl
    | L =>
      simp [step, hd] at hs; subst hs
      have hstep' : step δ ⟨l', r, q⟩ = some ⟨tail l', cons (l' 0) (cons w (tail r)), s⟩ := by simp [step, hd]
      by_cases h1 : 1 ≤ tn
      · simp [tnext, hd, h1] at ht; subst ht
        obtain ⟨a, u', rfl, -⟩ := app_length_cons (X := X) (show 1 ≤ u.length by omega)
        have ha : l 0 = a := by rw [hlX]; rfl
        have ha' : l' 0 = a := by rw [hl'X]; rfl
        refine ⟨0, _, steps_one δ hstep', ?_⟩
        refine relL rfl ?_ u' X (by simp at hu ⊢; omega) ?_ ?_
        · show cons (l 0) (cons w (tail r)) = cons (l' 0) (cons w (tail r)); rw [ha, ha']
        · show tail l = _; rw [hlX]; rfl
        · show tail l' = _; rw [hl'X]; rfl
      · have htn : tn = 0 := by omega
        subst htn
        have hu' : u = [] := by simpa using hu
        subst hu'
        have hlX0 : l = X := hlX
        have hl'X0 : l' = app tv X := hl'X
        subst hlX0
        cases tv with
        | nil =>
          simp [tnext, hd] at ht; subst ht
          have : l' = l := hl'X0
          subst this
          exact ⟨0, _, steps_one δ hstep', relR rfl rfl (Nat.le_refl 1) [l' 0] (cons w (tail r)) rfl rfl rfl⟩
        | cons a vt =>
          have shift : a = l 0 → t' = ⟨false, 0, rotL (a :: vt)⟩ →
              ∃ k d', steps δ (k + 1) ⟨l', r, q⟩ = some d' ∧
                Rel t' ⟨tail l, cons (l 0) (cons w (tail r)), s⟩ d' := by
            intro hh ht'
            subst ht'
            have hX : l = cons a (tail l) := by rw [hh]; exact (cons_head_tail l).symm
            have hl'2 : l' = cons a (app (rotL (a :: vt)) (tail l)) := by
              rw [hl'X0, ← app_rotL, ← hX]
            refine ⟨0, _, steps_one δ hstep', ?_⟩
            refine relL rfl ?_ [] (tail l) rfl rfl ?_
            · show cons (l 0) (cons w (tail r)) = cons (l' 0) (cons w (tail r))
              rw [hl'2, ← hh]; rfl
            · show tail l' = app (rotL (a :: vt)) (tail l)
              rw [hl'2]; rfl
          simp only [tnext, hd, show ¬ 1 ≤ 0 by omega] at ht
          rcases hz : zsim δ fuel vt [a] s with _ | z
          · rw [hz] at ht
            by_cases hh : a = l 0
            · simp [hh] at ht; exact shift hh (by rw [← ht, ← hh])
            · simp [hh] at ht
          · rw [hz] at ht
            cases z with
            | right lw s' k =>
              by_cases hh : a = l 0
              · simp [hh] at ht; exact shift hh (by rw [← ht, ← hh])
              · simp [hh] at ht
            | left rw s' k =>
              by_cases hs' : s' = s
              · subst hs'
                simp at ht; subst ht
                have hc := zsim_sound δ fuel vt [a] s' _ hz l (cons w (tail r))
                refine ⟨k, ⟨tail l, cons (l 0) (app rw (cons w (tail r))), s'⟩, ?_, ?_⟩
                · have e1 : tail l' = app vt l := by rw [hl'X0]; rfl
                  have e2 : l' 0 = a := by rw [hl'X0]; rfl
                  rw [e1, e2] at hstep'
                  exact steps_succ' δ hstep' hc
                · exact relR rfl rfl (Nat.le_refl 1) [l 0] (cons w (tail r)) rfl rfl rfl
              · simp only [hs', ite_false] at ht
                by_cases hh : a = l 0
                · simp [hh] at ht; exact shift hh (by rw [← ht, ← hh])
                · simp [hh] at ht

/-- Halting is decided by the cell under the head, which the two configurations share. -/
theorem rel_halt {t : Ins} {c c' : Cfg Q} (hr : Rel t c c') : step δ c = none ↔ step δ c' = none := by
  obtain ⟨l, r, q⟩ := c
  obtain ⟨l', r', q'⟩ := c'
  obtain ⟨hq, hrest⟩ := hr
  simp only at hq; subst hq
  have h0 : r 0 = r' 0 := by
    obtain ⟨tr, tn, tv⟩ := t
    cases tr
    · obtain ⟨hrr, -⟩ := hrest; simp only at hrr; rw [hrr]
    · obtain ⟨-, hn, u, X, hu, hrX, hr'X⟩ := hrest
      obtain ⟨a, u', rfl, -⟩ := app_length_cons (X := X) (show 1 ≤ u.length by omega)
      simp only at hrX hr'X; rw [hrX, hr'X]; rfl
  simp only [step, h0]
  constructor <;> intro h
  · rcases hd : δ q (r' 0) with _ | ⟨w, d, s⟩
    · rfl
    · rw [hd] at h; cases d <;> simp at h
  · rcases hd : δ q (r' 0) with _ | ⟨w, d, s⟩
    · rfl
    · rw [hd] at h; cases d <;> simp at h

/-- The followed run: `none` once it reaches a bad moment; it stops at a halt of `c`. -/
def trk (fuel : Nat) : Nat → Ins → Cfg Q → Option (Ins × Cfg Q)
  | 0, t, c => some (t, c)
  | m + 1, t, c =>
    match step δ c with
    | none => some (t, c)
    | some d =>
      match tnext δ fuel t c with
      | none => none
      | some t' => trk fuel m t' d

/-- The followed run never reaches a bad moment. -/
def Good (fuel : Nat) (t : Ins) (c : Cfg Q) : Prop := ∀ m, trk δ fuel m t c ≠ none

theorem good_step {fuel : Nat} {t t' : Ins} {c d : Cfg Q} (hG : Good δ fuel t c) (hs : step δ c = some d)
    (ht : tnext δ fuel t c = some t') : Good δ fuel t' d := by
  intro m h
  apply hG (m + 1)
  simp only [trk, hs, ht]; exact h

theorem good_tnext {fuel : Nat} {t : Ins} {c d : Cfg Q} (hG : Good δ fuel t c) (hs : step δ c = some d) :
    ∃ t', tnext δ fuel t c = some t' := by
  rcases h : tnext δ fuel t c with _ | t'
  · exact absurd (by simp [trk, hs, h]) (hG 1)
  · exact ⟨t', rfl⟩

/-- Every run of `c` is matched by a run of `c'` at least as long. -/
theorem rel_run {fuel : Nat} : ∀ (n : Nat) {t : Ins} {c c' e : Cfg Q}, Rel t c c' → Good δ fuel t c →
    steps δ n c = some e → ∃ N t' e', n ≤ N ∧ steps δ N c' = some e' ∧ Rel t' e e' := by
  intro n
  induction n with
  | zero =>
    intro t c c' e hr _ h
    simp at h; subst h
    exact ⟨0, t, c', Nat.le_refl 0, rfl, hr⟩
  | succ n ih =>
    intro t c c' e hr hG h
    rcases hs : step δ c with _ | d
    · simp [steps, hs] at h
    · rw [steps_succ_of_step δ n hs] at h
      obtain ⟨t', ht⟩ := good_tnext δ hG hs
      obtain ⟨k, d', hk, hr'⟩ := rel_step δ hr hs ht
      obtain ⟨N, t'', e', hN, hN', hr''⟩ := ih hr' (good_step δ hG hs ht) h
      refine ⟨k + 1 + N, t'', e', by omega, steps_seq δ hk hN', hr''⟩

theorem all_steps_of_not_halts {c : Cfg Q} (h : ¬ Halts δ c) : ∀ n, ∃ e, steps δ n c = some e := by
  intro n
  induction n generalizing c with
  | zero => exact ⟨c, rfl⟩
  | succ n ih =>
    rcases hs : step δ c with _ | d
    · exact absurd ⟨0, c, rfl, hs⟩ h
    · rw [steps_succ_of_step δ n hs]
      apply ih
      rintro ⟨m, e, he, hh⟩
      exact h ⟨m + 1, e, by rw [steps_succ_of_step δ m hs]; exact he, hh⟩

/-- **Halting together.**  If `c'` is `c` with a word inserted and the followed run of `c` never reaches a bad
moment, the two configurations both halt or both run forever. -/
theorem halts_iff_of_good {fuel : Nat} {t : Ins} {c c' : Cfg Q} (hr : Rel t c c') (hG : Good δ fuel t c) :
    Halts δ c ↔ Halts δ c' := by
  constructor
  · rintro ⟨n, e, he, hh⟩
    obtain ⟨N, t', e', -, hN, hr'⟩ := rel_run δ n hr hG he
    exact ⟨N, e', hN, (rel_halt δ hr').1 hh⟩
  · intro h'
    apply Classical.byContradiction; intro hc
    have hall := all_steps_of_not_halts δ hc
    apply not_halts_of_forall δ (c := c') _ h'
    apply forall_of_unbounded δ (fun _ => True) (fun n => ?_) (fun m _ => ?_)
    · exact ⟨n, Nat.le_refl n, trivial⟩
    · -- every length `m` of the run of `c'` is covered by a run of `c` of length `m`
      obtain ⟨e, he⟩ := hall m
      obtain ⟨N, t', e', hmN, hN, -⟩ := rel_run δ m hr hG he
      have e2 : N = m + (N - m) := by omega
      rw [e2] at hN
      exact steps_le δ hN

/-! ## Finite tapes -/

theorem app_replicate_false (k : Nat) : app (List.replicate k false) blank = blank := by
  induction k with
  | zero => rfl
  | succ k ih => show cons false (app (List.replicate k false) blank) = blank; rw [ih, cons_false_blank]

theorem app_pad (w : List Bool) (k : Nat) : app (w ++ List.replicate k false) blank = app w blank := by
  rw [← app_app, app_replicate_false]

/-- Two finite words describe the same tape when they agree after padding with blanks. -/
theorem app_blank_eq (a b : List Bool)
    (h : a ++ List.replicate (b.length - a.length) false = b ++ List.replicate (a.length - b.length) false) :
    app a blank = app b blank := by
  rw [← app_pad a (b.length - a.length), h, app_pad]

/-! ## Renamed and mirrored tables -/

/-- A map of configurations that commutes with one step keeps halting. -/
theorem halts_of_map {Q' : Type} (δ' : Q' → Bool → Option (Bool × Dir × Q'))
    (φ : Cfg Q → Cfg Q') (hφ : ∀ c, step δ' (φ c) = (step δ c).map φ) (c : Cfg Q) :
    Halts δ c ↔ Halts δ' (φ c) := by
  have hs : ∀ n (c : Cfg Q), steps δ' n (φ c) = (steps δ n c).map φ := by
    intro n
    induction n with
    | zero => intro c; rfl
    | succ n ih =>
      intro c
      simp only [steps, hφ c]
      rcases step δ c with _ | c'
      · rfl
      · exact ih c'
  constructor
  · rintro ⟨n, d, hd, hh⟩
    exact ⟨n, φ d, by rw [hs, hd]; rfl, by rw [hφ, hh]; rfl⟩
  · rintro ⟨n, d', hd', hh'⟩
    rw [hs] at hd'
    rcases h : steps δ n c with _ | d
    · rw [h] at hd'; cases hd'
    · rw [h] at hd'
      cases hd'
      refine ⟨n, d, h, ?_⟩
      rw [hφ] at hh'
      rcases h2 : step δ d with _ | e
      · rfl
      · rw [h2] at hh'; cases hh'

def Dir.flip : Dir → Dir
  | .L => .R
  | .R => .L

/-- The mirror image of a configuration, the states renamed by `f`. -/
def mirrorCfg {Q' : Type} (f : Q → Q') (c : Cfg Q) : Cfg Q' := ⟨tail c.r, cons (c.r 0) c.l, f c.st⟩

theorem step_mirrorCfg {Q' : Type} (δ' : Q' → Bool → Option (Bool × Dir × Q')) (f : Q → Q')
    (hδ : ∀ q b, δ' (f q) b = (δ q b).map (fun t => (t.1, t.2.1.flip, f t.2.2))) (c : Cfg Q) :
    step δ' (mirrorCfg f c) = (step δ c).map (mirrorCfg f) := by
  obtain ⟨l, r, q⟩ := c
  rcases h : δ q (r 0) with _ | ⟨w, d, s⟩
  · simp [step, mirrorCfg, hδ, h]
  · cases d
    · simp [step, mirrorCfg, hδ, h, Dir.flip]
      exact (cons_head_tail l).symm
    · simp [step, mirrorCfg, hδ, h, Dir.flip]

/-- The states renamed by `f`. -/
def renameCfg {Q' : Type} (f : Q → Q') (c : Cfg Q) : Cfg Q' := ⟨c.l, c.r, f c.st⟩

theorem step_renameCfg {Q' : Type} (δ' : Q' → Bool → Option (Bool × Dir × Q')) (f : Q → Q')
    (hδ : ∀ q b, δ' (f q) b = (δ q b).map (fun t => (t.1, t.2.1, f t.2.2))) (c : Cfg Q) :
    step δ' (renameCfg f c) = (step δ c).map (renameCfg f) := by
  obtain ⟨l, r, q⟩ := c
  rcases h : δ q (r 0) with _ | ⟨w, d, s⟩
  · simp [step, renameCfg, hδ, h]
  · cases d <;> simp [step, renameCfg, hδ, h]

theorem mirrorCfg_blank {Q' : Type} (f : Q → Q') (q : Q) : mirrorCfg f (blankCfg q) = blankCfg (f q) := by
  show (⟨tail blank, cons false blank, f q⟩ : Cfg Q') = ⟨blank, blank, f q⟩
  rw [cons_false_blank]; rfl

theorem steps_add_split : ∀ (a b : Nat) {c d e : Cfg Q}, steps δ a c = some d → steps δ (a + b) c = some e →
    steps δ b d = some e := by
  intro a
  induction a with
  | zero => intro b c d e h1 h2; simp at h1; subst h1; simpa using h2
  | succ a ih =>
    intro b c d e h1 h2
    rcases hs : step δ c with _ | c'
    · simp [steps, hs] at h1
    · rw [steps_succ_of_step δ a hs] at h1
      have e3 : a + 1 + b = (a + b) + 1 := by omega
      rw [e3, steps_succ_of_step δ (a + b) hs] at h2
      exact ih b h1 h2


/-- A run reached after `n` steps halts exactly when the run from its start does. -/
theorem halts_iff_of_steps' {n : Nat} {c d : Cfg Q} (h : steps δ n c = some d) : Halts δ c ↔ Halts δ d := by
  constructor
  · rintro ⟨m, e, he, hh⟩
    by_cases hmn : n ≤ m
    · have e2 : m = n + (m - n) := by omega
      rw [e2] at he
      have := steps_add_split δ n (m - n) h he
      exact ⟨m - n, e, this, hh⟩
    · -- the halt comes before step n, contradiction with `h`
      have e2 : n = m + ((n - m - 1) + 1) := by omega
      rw [e2, steps_halt δ he hh] at h; cases h
  · rintro ⟨m, e, he, hh⟩
    exact ⟨n + m, e, steps_seq δ h he, hh⟩

end TM
