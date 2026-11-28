import Visit

/-! # A visit interpreter on tokens of two cells, proved sound once

`Visit.lean` proves rows of the visit law one at a time.  Here the rows are not listed: `tv` runs the machine on the
first token of a list of tokens (two cells), and each time the head leaves the token to the right it calls itself on
the rest of the list (a nested visit), until the head leaves the token to the left.  `tv_sound` proves once, for every
list, that what `tv` computes is what the machine does (`Vis`), with blank tape after the list.  So any law about
visits of such tapes can be proved by computing with `tv` on lists, by induction on the lists, without tapes.

`tv n q ts` is `none` when the fuel `n` runs out or the machine halts; it never claims a wrong result. -/

namespace H64715

open TM

/-- A token: two cells. -/
abbrev Tok := Bool × Bool

/-- The tokens in front of a tape. -/
def tT : List Tok → Tape → Tape
  | [], s => s
  | t :: ts, s => cons t.1 (cons t.2 (tT ts s))

/-- The tokens in front of blank tape. -/
abbrev tB (ts : List Tok) : Tape := tT ts blank

mutual
/-- A visit of the tokens `ts` (then blank tape) in state `q`: the state it leaves in, and the tokens after it. -/
def tv : Nat → St → List Tok → Option (St × List Tok)
  | 0, _, _ => none
  | n + 1, q, [] => tv n q [(false, false)]
  | n + 1, q, t :: ts => match run n q t.1 t.2 false ts with
    | none => none
    | some (r, t', ts') => some (r, t' :: ts')
/-- The head inside the token `(c0, c1)` (on `c1` if `pos`, else on `c0`) in state `q`, with the tokens `ts` after it:
run until the head leaves the token to the left. -/
def run : Nat → St → Bool → Bool → Bool → List Tok → Option (St × Tok × List Tok)
  | 0, _, _, _, _, _ => none
  | n + 1, q, c0, c1, pos, ts =>
    match trans q (if pos then c1 else c0) with
    | none => none
    | some (w, .L, q') => if pos then run n q' c0 w false ts else some (q', (w, c1), ts)
    | some (w, .R, q') =>
      if pos then
        match tv n q' ts with
        | none => none
        | some (r, ts') => run n r c0 w true ts'
      else run n q' w c1 true ts
end

theorem tB_nil : tB [] = tB [(false, false)] := by
  show blank = cons false (cons false blank)
  rw [cons_false_blank, cons_false_blank]

theorem step_eq {q q' : St} {c w : Bool} {d : Dir} (h : trans q c = some (w, d, q')) (l r : Tape) (hr : r 0 = c) :
    step ⟨l, r, q⟩ = (match d with
      | .R => some ⟨cons w l, tail r, q'⟩
      | .L => some ⟨tail l, cons (l 0) (cons w (tail r)), q'⟩) := by
  cases d <;> simp [step, TM.step, hr, h]

theorem steps_more {c c' : Config} {k : Nat} {x : Option Config} (h : step c = some c') (hk : steps k c' = x) :
    steps (k + 1) c = x := by
  show TM.steps trans (k + 1) c = x
  rw [TM.steps_succ_of_step trans k h]; exact hk

/-- Soundness, both functions at once, by induction on the fuel. -/
theorem sound (n : Nat) :
    (∀ q ts r ts', tv n q ts = some (r, ts') → Vis q (tB ts) r (tB ts')) ∧
    (∀ q c0 c1 pos ts r t' ts', run n q c0 c1 pos ts = some (r, t', ts') →
      ∀ (a : Bool) (L : Tape), ∃ k, steps k
        (if pos then ⟨cons c0 (cons a L), cons c1 (tB ts), q⟩ else ⟨cons a L, cons c0 (cons c1 (tB ts)), q⟩) =
        some ⟨L, cons a (cons t'.1 (cons t'.2 (tB ts'))), r⟩) := by
  induction n with
  | zero => exact ⟨fun _ _ _ _ h => by simp [tv] at h, fun _ _ _ _ _ _ _ _ h => by simp [run] at h⟩
  | succ n ih =>
    obtain ⟨ihv, ihr⟩ := ih
    refine ⟨?_, ?_⟩
    · intro q ts r ts' h
      cases ts with
      | nil =>
        simp only [tv] at h
        rw [tB_nil]
        exact ihv _ _ _ _ h
      | cons t ts =>
        simp only [tv] at h
        cases hr : run n q t.1 t.2 false ts with
        | none => simp [hr] at h
        | some x =>
          obtain ⟨r0, t0, ts0⟩ := x
          simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨e1, e2⟩ := h
          subst e1; subst e2
          intro a L
          obtain ⟨k, hk⟩ := ihr _ _ _ _ _ _ _ _ hr a L
          exact ⟨k, hk⟩
    · intro q c0 c1 pos ts r t' ts' h a L
      cases pos with
      | true =>
        show ∃ k, steps k ⟨cons c0 (cons a L), cons c1 (tB ts), q⟩ = _
        simp only [run, ite_true] at h
        cases ht : trans q c1 with
        | none => simp [ht] at h
        | some y =>
          obtain ⟨w, d, q'⟩ := y
          cases d with
          | L =>
            simp only [ht] at h
            obtain ⟨k, hk⟩ := ihr _ _ _ _ _ _ _ _ h a L
            exact ⟨k + 1, steps_more (by rw [step_eq ht _ _ rfl]; rfl) hk⟩
          | R =>
            simp only [ht] at h
            cases hv : tv n q' ts with
            | none => simp [hv] at h
            | some z =>
              obtain ⟨r1, ts1⟩ := z
              simp only [hv] at h
              obtain ⟨k1, hk1⟩ := ihv _ _ _ _ hv w (cons c0 (cons a L))
              obtain ⟨k2, hk2⟩ := ihr _ _ _ _ _ _ _ _ h a L
              refine ⟨1 + (k1 + k2), ?_⟩
              have s0 : steps 1 ⟨cons c0 (cons a L), cons c1 (tB ts), q⟩ =
                  some ⟨cons w (cons c0 (cons a L)), tB ts, q'⟩ :=
                steps_more (by rw [step_eq ht _ _ rfl]; rfl) rfl
              exact steps_seq trans s0 (steps_seq trans hk1 hk2)
      | false =>
        show ∃ k, steps k ⟨cons a L, cons c0 (cons c1 (tB ts)), q⟩ = _
        simp only [run, Bool.false_eq_true, ite_false] at h
        cases ht : trans q c0 with
        | none => simp [ht] at h
        | some y =>
          obtain ⟨w, d, q'⟩ := y
          cases d with
          | L =>
            simp only [ht, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨e1, e2, e3⟩ := h
            subst e1; subst e2; subst e3
            exact ⟨1, steps_more (by rw [step_eq ht _ _ rfl]; rfl) rfl⟩
          | R =>
            simp only [ht] at h
            obtain ⟨k, hk⟩ := ihr _ _ _ _ _ _ _ _ h a L
            exact ⟨k + 1, steps_more (by rw [step_eq ht _ _ rfl]; rfl) hk⟩

/-- **The interpreter is sound**: what `tv` computes is a visit of the machine. -/
theorem tv_sound {n : Nat} {q r : St} {ts ts' : List Tok} (h : tv n q ts = some (r, ts')) :
    Vis q (tB ts) r (tB ts') :=
  (sound n).1 q ts r ts' h

end H64715
