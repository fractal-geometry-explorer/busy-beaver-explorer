import Race

/-!
# The windows after E reads the last 1 during a crossing

`astep` can fail only at a crossing turn with blank end (`End.lean`), and not at all when the frozen word has a
witness and the far part is clean (`Race.lean`).  In the first 40,000 list steps 10 crossing turns with blank end have
no witness.  All of them come in the first bounces after an `EO` turn during a crossing (E on the last 1, which
erases it, so the end is blank from then on).  There are six such turns, with three near parts:

* `b a b a^6` (four times): `window_W3`, two list steps;
* `b a b a^12` (once): `window_W6`, three list steps;
* a 43-letter near part (once, list step 28,450): `window_W43`, six list steps, if the far part starts `u v v`.

Each theorem holds for every clean far part (any prefix `p`): within that many list steps `astep` does not fail and
reaches a state that is `Safe`: the crossing is over (`Plain`), or the frozen word has a witness and the far part is
clean (`Witnessed`, whose next step exists by `witnessed_step`).  So the ten turns are covered by theorems about
whole families of list states, not only the states of the run.

What the window needs from the far part: `eo_W1_fails` shows that `EO (b a b a^2)` fails at once for every far part.
The run reaches `b a b a^6` because the far part's first run is `u v v` (`2 + 2·2` letters `a` join the near part);
a far part starting `u u` would give `b a b a^2`.  `py/game.py` finds such failures from real states of the run when
the far part is left free.  So what remains is about the far parts the growing phase builds, not about the near part.
-/

namespace H75625
open TM

/-! ## Lists of `a`s -/

theorem coreO_falses (m : Nat) (O : List Bool) (p : Bool) (t : List Bool) (r : Bool) :
    ∀ N, coreO N (List.replicate m false ++ O) p t r = coreO (N ++ List.replicate m false) O p t r := by
  induction m with
  | zero => intro N; simp
  | succ m ih =>
    intro N
    show coreO (N ++ [false]) (List.replicate m false ++ O) p t r = _
    rw [ih, List.append_assoc]
    rfl

theorem dbl_append (xs ys : List Bool) : dbl (xs ++ ys) = dbl xs ++ dbl ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [dbl, ih]

theorem dbl_falses (z : Nat) : dbl (List.replicate z false) = List.replicate (2 * z) false := by
  induction z with
  | zero => rfl
  | succ z ih =>
    rw [List.replicate_succ, show 2 * (z + 1) = (2 * z + 1) + 1 by omega, List.replicate_succ, List.replicate_succ]
    simp [dbl, two, ih]

theorem par_append (xs ys : List Bool) : ∀ q, par q (xs ++ ys) = par (par q xs) ys := by
  induction xs with
  | nil => intro q; rfl
  | cons x xs ih => intro q; simp [par, ih]

theorem sx_falses (m : Nat) : ∀ q, sx q (List.replicate m false) = List.replicate m q := by
  induction m with
  | zero => intro q; rfl
  | succ m ih => intro q; simp [List.replicate_succ, sx, ih]

theorem par_falses (m : Nat) : ∀ q, par q (List.replicate m false) = q := by
  induction m with
  | zero => intro q; rfl
  | succ m ih => intro q; simp [List.replicate_succ, par, ih]

theorem rswL_falses (m : Nat) : ∀ (W xs : List Bool),
    rswL false W (List.replicate m false ++ xs) = rswL false (List.replicate m false ++ W) xs := by
  induction m with
  | zero => intro W xs; rfl
  | succ m ih =>
    intro W xs
    show rswL false (false :: W) (List.replicate m false ++ xs) = _
    rw [ih, List.replicate_succ', List.append_assoc]
    rfl

theorem rswL_trues2 (k : Nat) : ∀ (W xs : List Bool),
    rswL false W (List.replicate (2 * k) true ++ xs) = rswL false ((List.replicate k [false, true]).flatten ++ W) xs := by
  induction k with
  | zero => intro W xs; rfl
  | succ k ih =>
    intro W xs
    have e : List.replicate (2 * (k + 1)) true ++ xs = true :: true :: (List.replicate (2 * k) true ++ xs) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by omega]; rfl
    rw [e]
    show rswL false (false :: true :: W) (List.replicate (2 * k) true ++ xs) = _
    rw [ih]
    congr 1
    rw [List.replicate_succ', List.flatten_append]
    simp

/-- Every word is a run of `false`s, then nothing or a `true`. -/
theorem split_falses (ws : List Bool) :
    ∃ z, ws = List.replicate z false ∨ ∃ ws', ws = List.replicate z false ++ true :: ws' := by
  induction ws with
  | nil => exact ⟨0, Or.inl rfl⟩
  | cons x ws ih =>
    cases x with
    | true => exact ⟨0, Or.inr ⟨ws, rfl⟩⟩
    | false =>
      obtain ⟨z, h | ⟨ws', h⟩⟩ := ih
      · exact ⟨z + 1, Or.inl (by rw [h]; rfl)⟩
      · exact ⟨z + 1, Or.inr ⟨ws', by rw [h]; rfl⟩⟩

/-! ## Steps that cannot fail -/

theorem endS_none (W : List Bool) (e r p : Bool) : (endS W e r none p).isSome := by
  cases e <;> cases r <;> rfl

theorem fromSweep_none (p r : Bool) (x : List Bool × Bool × Option (List Bool)) : (fromSweep none p r x).isSome := by
  obtain ⟨W, e, o⟩ := x
  cases o with
  | none => exact endS_none W e r p
  | some _ => rfl

theorem coreP_isSome (w : List Bool) (p : Bool) (t : List Bool) (r : Bool) : (coreP w p t r).isSome :=
  fromSweep_none _ _ _

theorem coreO_nil (N : List Bool) (p : Bool) (t : List Bool) (r : Bool) : (coreO N [] p t r).isSome := by
  cases p
  · exact coreP_isSome _ _ _ _
  · exact coreP_isSome _ _ _ _

/-- A far part in the shape the crossings keep: some `a`s, then a 4-cell word (`Crossing.lean`). -/
def Clean (O : List Bool) : Prop := ∃ m ws, O = List.replicate m false ++ dbl ws

theorem clean_split (O : List Bool) (h : Clean O) :
    ∃ m, O = List.replicate m false ∨ ∃ ws, O = List.replicate m false ++ dbl (true :: ws) := by
  obtain ⟨m, ws, rfl⟩ := h
  obtain ⟨z, h | ⟨ws', h⟩⟩ := split_falses ws <;> subst h
  · exact ⟨m + 2 * z, Or.inl (by rw [dbl_falses, List.replicate_append_replicate])⟩
  · exact ⟨m + 2 * z, Or.inr ⟨ws', by rw [dbl_append, dbl_falses, ← List.append_assoc, List.replicate_append_replicate]⟩⟩

/-- `astep_T2_witness` for every clean far part. -/
theorem witness_clean (N O : List Bool) (hO : Clean O) (p : Bool) (u : List Bool) (k : Nat) (v : List Bool)
    (hv : v.head? ≠ some true) (r : Bool) :
    (astep (.T2 N O p (u ++ false :: (List.replicate (2 * k + 1) true ++ v)) r)).isSome := by
  obtain ⟨m, h | ⟨ws, h⟩⟩ := clean_split O hO <;> subst h
  · show (coreO N (List.replicate m false) p _ r).isSome
    have e := coreO_falses m [] p (true :: (u ++ false :: (List.replicate (2 * k + 1) true ++ v))) r N
    rw [List.append_nil] at e
    rw [e]; exact coreO_nil _ _ _ _
  · show (coreO N (List.replicate m false ++ dbl (true :: ws)) p _ r).isSome
    rw [coreO_falses]
    exact astep_T2_witness (N ++ List.replicate m false) ws p u k v hv r

/-! ## How a window can end -/

/-- A list state the crossing is over at: what a bounce with no lone 1 in the zone returns (`coreP`). -/
def Plain : AS → Prop
  | .T .. => True
  | .EO _ none _ => True
  | .T2 [] _ _ [] true => True
  | _ => False

theorem coreP_plain (w : List Bool) (p : Bool) (t : List Bool) (r : Bool) (b : AS) (h : coreP w p t r = some b) :
    Plain b := by
  unfold coreP at h
  generalize rswL false [false] _ = x at h
  obtain ⟨W, e, o⟩ := x
  cases o <;> cases e <;> cases r <;> simp [fromSweep, endS] at h <;> subst h <;> trivial

theorem coreO_nil_plain (N : List Bool) (p : Bool) (t : List Bool) (r : Bool) (b : AS) (h : coreO N [] p t r = some b) :
    Plain b := by
  cases p
  · exact coreP_plain _ _ _ _ b h
  · exact coreP_plain _ _ _ _ b h

/-- A crossing turn with a clean far part and a witness in its frozen word: its next step exists (`witness_clean`). -/
def Witnessed : AS → Prop
  | .T2 _ O _ s _ => Clean O ∧ ∃ u k v, v.head? ≠ some true ∧ s = u ++ false :: (List.replicate (2 * k + 1) true ++ v)
  | _ => False

theorem witnessed_step (b : AS) (h : Witnessed b) : (astep b).isSome := by
  cases b with
  | T2 N O p s r =>
    obtain ⟨hO, u, k, v, hv, rfl⟩ := h
    exact witness_clean N O hO p u k v hv r
  | _ => exact h.elim

/-- The window has ended safely: the crossing is over, or a witness has appeared. -/
def Safe (b : AS) : Prop := Plain b ∨ Witnessed b

/-! ## The window after `EO (b a b a^6)` (four of the ten turns) -/

/-- **The near part alone is not safe**: `EO (b a b a^2)` fails at once, for every clean far part. -/
theorem eo_W1_fails (ws : List Bool) (p : Bool) :
    astep (.EO [true, false, true, false, false, false] (some (dbl (true :: ws))) p) = none := by
  rfl

def W3 : List Bool := [true, false, true, false, false, false, false, false, false]
def A3 : List Bool := [true, false, true, false, true, false, true]

theorem w3_step1 (ws : List Bool) (p : Bool) :
    astep (.EO W3 (some (dbl (true :: ws))) p) = some (.T2 A3 (false :: false :: dbl ws) p [false] false) := by
  rfl

theorem w3_step2 (ws : List Bool) (p : Bool) :
    ∃ b, astep (.T2 A3 (false :: false :: dbl ws) p [false] false) = some b ∧ Safe b := by
  obtain ⟨z, h | ⟨ws', h⟩⟩ := split_falses ws <;> subst h
  · have e : false :: false :: dbl (List.replicate z false) = List.replicate (2 * z + 2) false ++ [] := by
      rw [dbl_falses, List.append_nil]; rfl
    show ∃ b, coreO A3 (false :: false :: dbl (List.replicate z false)) p [true, false] false = some b ∧ Safe b
    rw [e, coreO_falses]
    cases hb : coreO (A3 ++ List.replicate (2 * z + 2) false) [] p [true, false] false with
    | none => have := coreO_nil (A3 ++ List.replicate (2 * z + 2) false) p [true, false] false; rw [hb] at this; cases this
    | some b => exact ⟨b, rfl, Or.inl (coreO_nil_plain _ _ _ _ b hb)⟩
  · have e : false :: false :: dbl (List.replicate z false ++ true :: ws') =
        List.replicate (2 * z + 2) false ++ (true :: false :: dbl ws') := by
      rw [dbl_append, dbl_falses]; rfl
    show ∃ b, coreO A3 (false :: false :: dbl (List.replicate z false ++ true :: ws')) p [true, false] false = some b ∧ Safe b
    rw [e, coreO_falses]
    have hp : par true (A3 ++ List.replicate (2 * z + 2) false) = true := by
      rw [par_append, par_falses]; rfl
    have hs : (sx true (A3 ++ List.replicate (2 * z + 2) false)).reverse ++ [true, false] =
        List.replicate (2 * (z + 1)) true ++ [true, false, false, true, true, false, false, true, false] := by
      rw [sx_append, sx_falses, List.reverse_append, List.reverse_replicate, List.append_assoc]
      rfl
    simp only [coreO, hp, ↓reduceIte, hs, rswL_trues2]
    refine ⟨_, rfl, Or.inr ⟨⟨2, ws', rfl⟩, [false, true, true, false], 0, [false], by simp, rfl⟩⟩

/-- The list machine reaches a safe state within `k` steps. -/
def SafeWithin : Nat → AS → Prop
  | 0, a => Safe a
  | k + 1, a => Safe a ∨ ∃ b, astep a = some b ∧ SafeWithin k b

theorem safeWithin_of_step (k : Nat) (a b : AS) (h : astep a = some b) (hb : SafeWithin k b) : SafeWithin (k + 1) a :=
  Or.inr ⟨b, h, hb⟩

theorem safeWithin_of_safe (k : Nat) (a : AS) (h : Safe a) : SafeWithin k a := by
  cases k with
  | zero => exact h
  | succ k => exact Or.inl h

/-- **The window after `EO (b a b a^6)` is safe for every clean far part**: within two list steps the crossing is
over or a witness has appeared. -/
theorem window_W3 (ws : List Bool) (p : Bool) : SafeWithin 2 (.EO W3 (some (dbl (true :: ws))) p) := by
  obtain ⟨b, hb, hs⟩ := w3_step2 ws p
  exact safeWithin_of_step _ _ _ (w3_step1 ws p) (safeWithin_of_step _ _ _ hb (safeWithin_of_safe 0 b hs))


/-! ## The window after `EO (b a b a^12)` (two of the ten turns) -/

def W6 : List Bool := [true, false, true] ++ List.replicate 12 false
def A6 : List Bool := [true, false, true, false, true, false, true, false, true, false, true, false, true]
def C6 : List Bool := [true, false, false, false, true, false, false, false, true, false, false, false, true]

theorem w6_step1 (ws : List Bool) (p : Bool) :
    astep (.EO W6 (some (dbl (true :: ws))) p) = some (.T2 A6 (false :: false :: dbl ws) p [false] false) := by
  rfl

/-- The third bounce: an odd one, which leaves the witness `0 1` at the end of the frozen word. -/
theorem w6_step3 (z : Nat) (Y : List Bool) (p : Bool) :
    ∃ b, astep (.T2 ((C6 ++ [false]) ++ List.replicate (2 * z + 2) false) (false :: dbl (true :: Y)) p [] false) = some b ∧
      Safe b := by
  have e : ((C6 ++ [false]) ++ List.replicate (2 * z + 2) false) ++ [false] = C6 ++ List.replicate (2 * z + 4) false := by
    rw [show 2 * z + 4 = (2 * z + 2) + 1 + 1 by omega]
    simp only [List.append_assoc]
    rw [← List.replicate_succ']
    rfl
  show ∃ b, coreO (((C6 ++ [false]) ++ List.replicate (2 * z + 2) false) ++ [false]) (true :: false :: dbl Y) p [true]
    false = some b ∧ Safe b
  rw [e]
  have hp : par true (C6 ++ List.replicate (2 * z + 4) false) = true := by
    rw [par_append, par_falses]; rfl
  have hs : (sx true (C6 ++ List.replicate (2 * z + 4) false)).reverse ++ [true] =
      List.replicate (2 * (z + 2)) true ++ ((sx true C6).reverse ++ [true]) := by
    rw [sx_append, sx_falses, List.reverse_append, List.reverse_replicate, List.append_assoc]
    rfl
  simp only [coreO, hp, ↓reduceIte, hs, rswL_trues2]
  exact ⟨_, rfl, Or.inr ⟨⟨2, Y, rfl⟩, [false, false, false, true, true, true, true, false, false, false], 0, [],
    by simp, rfl⟩⟩

theorem w6_step2 (ws : List Bool) (p : Bool) :
    ∃ b, astep (.T2 A6 (false :: false :: dbl ws) p [false] false) = some b ∧ SafeWithin 1 b := by
  obtain ⟨z, h | ⟨ws', h⟩⟩ := split_falses ws <;> subst h
  · have e : false :: false :: dbl (List.replicate z false) = List.replicate (2 * z + 2) false ++ [] := by
      rw [dbl_falses, List.append_nil]; rfl
    show ∃ b, coreO A6 (false :: false :: dbl (List.replicate z false)) p [true, false] false = some b ∧ SafeWithin 1 b
    rw [e, coreO_falses]
    cases hb : coreO (A6 ++ List.replicate (2 * z + 2) false) [] p [true, false] false with
    | none => have := coreO_nil (A6 ++ List.replicate (2 * z + 2) false) p [true, false] false; rw [hb] at this; cases this
    | some b => exact ⟨b, rfl, safeWithin_of_safe 1 b (Or.inl (coreO_nil_plain _ _ _ _ b hb))⟩
  · have e : false :: false :: dbl (List.replicate z false ++ true :: ws') =
        List.replicate (2 * z + 2) false ++ (true :: false :: dbl ws') := by
      rw [dbl_append, dbl_falses]; rfl
    show ∃ b, coreO A6 (false :: false :: dbl (List.replicate z false ++ true :: ws')) p [true, false] false = some b ∧
      SafeWithin 1 b
    rw [e, coreO_falses]
    have hp : par true (A6 ++ List.replicate (2 * z + 2) false) = false := by
      rw [par_append, par_falses]; rfl
    have hs : (sx true (A6 ++ List.replicate (2 * z + 2) false)).reverse ++ [true, false] =
        List.replicate (2 * z + 2) false ++ ((sx true A6).reverse ++ [true, false]) := by
      rw [sx_append, sx_falses, List.reverse_append, List.reverse_replicate, List.append_assoc]
      rfl
    have hf := far_even ws'
    simp only [dbl, two, List.cons_append, List.nil_append] at hf
    have h2 : coreO (A6 ++ List.replicate (2 * z + 2) false) (true :: false :: dbl ws') p [true, false] false =
        some (.T2 ((C6 ++ [false]) ++ List.replicate (2 * z + 2) false) (false :: dbl (true :: sx true ws'))
          (bne p (par false (true :: false :: dbl ws'))) [] false) := by
      simp only [coreO, hp, Bool.false_eq_true, ↓reduceIte, hf, hs, rswL_falses, List.append_nil]
      rfl
    rw [h2]
    obtain ⟨b, hb, hsafe⟩ := w6_step3 z (sx true ws') (bne p (par false (true :: false :: dbl ws')))
    exact ⟨_, rfl, safeWithin_of_step 0 _ b hb (safeWithin_of_safe 0 b hsafe)⟩

/-- **The window after `EO (b a b a^12)` is safe for every clean far part** (within three list steps). -/
theorem window_W6 (ws : List Bool) (p : Bool) : SafeWithin 3 (.EO W6 (some (dbl (true :: ws))) p) := by
  obtain ⟨b, hb, hs⟩ := w6_step2 ws p
  exact safeWithin_of_step _ _ _ (w6_step1 ws p) (safeWithin_of_step _ _ _ hb hs)


/-! ## One crossing bounce with a clean far part `dbl (true :: X)`, for any `X` -/

theorem core_odd (N X : List Bool) (p : Bool) (t : List Bool) (r : Bool) (h : par true N = true) :
    coreO N (dbl (true :: X)) p t r =
      fromSweep (some (false :: false :: dbl X)) p r (rswL false [] ((sx true N).reverse ++ t)) := by
  simp only [dbl, two, List.cons_append, List.nil_append, coreO, h, ↓reduceIte]

theorem core_even (N X : List Bool) (p : Bool) (t : List Bool) (r : Bool) (h : par true N = false) :
    coreO N (dbl (true :: X)) p t r =
      fromSweep (some (false :: dbl (true :: sx true X))) (bne p (par false (dbl (true :: X)))) r
        (rswL false [] ((sx true N).reverse ++ t)) := by
  have hf := far_even X
  simp only [dbl, two, List.cons_append, List.nil_append] at hf ⊢
  simp only [coreO, h, Bool.false_eq_true, ↓reduceIte, hf]

/-! ## The window after list step 28,450 (four of the ten turns)

The zone is 43 letters; the far part only has to start with `u v v` (`dbl (true :: false :: false :: Y)`).  Written by
`py/window43.py`. -/

def W43 : List Bool := [true, false, true, false, false, true, false, false, false, false, true, false, true, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

theorem w43_step1 (Y : List Bool) (p : Bool) :
    ∃ q, astep (.EO W43 (some (dbl (true :: false :: false :: Y))) p) = some (.T2 [true, false, true, false, false, false, false, false, false, true, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] (false :: dbl (true :: sx true (false :: false :: Y))) q [false] false) := by
  refine ⟨bne p (par false (dbl (true :: (false :: false :: Y)))), ?_⟩
  show coreO [true, false, true, false, false, true, false, false, false, false, true, false, true, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] (dbl (true :: (false :: false :: Y))) p [] false = _
  rw [core_even _ _ _ _ _ rfl]
  rfl

theorem w43_step2 (Y : List Bool) (p : Bool) :
    ∃ q, astep (.T2 [true, false, true, false, false, false, false, false, false, true, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] (false :: dbl (true :: sx true (false :: false :: Y))) p [false] false) = some (.T2 [true, false, true, false, true, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] (false :: dbl (true :: sx true (sx true (false :: false :: Y)))) q [false, true, false] false) := by
  refine ⟨bne p (par false (dbl (true :: (sx true (false :: false :: Y))))), ?_⟩
  show coreO [true, false, true, false, false, false, false, false, false, true, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] (dbl (true :: (sx true (false :: false :: Y)))) p (true :: [false]) false = _
  rw [core_even _ _ _ _ _ rfl]
  rfl

theorem w43_step3 (Y : List Bool) (p : Bool) :
    ∃ q, astep (.T2 [true, false, true, false, true, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] (false :: dbl (true :: sx true (sx true (false :: false :: Y)))) p [false, true, false] false) = some (.T2 [true, false, false, false, true, false, false, false, true, false, true, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] (false :: dbl (true :: sx true (sx true (sx true (false :: false :: Y))))) q [true, false] false) := by
  refine ⟨bne p (par false (dbl (true :: (sx true (sx true (false :: false :: Y)))))), ?_⟩
  show coreO [true, false, true, false, true, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] (dbl (true :: (sx true (sx true (false :: false :: Y))))) p (true :: [false, true, false]) false = _
  rw [core_even _ _ _ _ _ rfl]
  rfl

theorem w43_step4 (Y : List Bool) (p : Bool) :
    ∃ q, astep (.T2 [true, false, false, false, true, false, false, false, true, false, true, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] (false :: dbl (true :: sx true (sx true (sx true (false :: false :: Y))))) p [true, false] false) = some (.T2 [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true] (false :: false :: dbl (sx true (sx true (sx true (false :: false :: Y))))) q [false, true, true, false, false, true, true, true, true, false, false, false, false, true, true, false] false) := by
  refine ⟨p, ?_⟩
  show coreO [true, false, false, false, true, false, false, false, true, false, true, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] (dbl (true :: (sx true (sx true (sx true (false :: false :: Y)))))) p (true :: [true, false]) false = _
  rw [core_odd _ _ _ _ _ rfl]
  rfl

theorem w43_step5 (Y : List Bool) (p : Bool) :
    ∃ q, astep (.T2 [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true] (false :: false :: dbl (sx true (sx true (sx true (false :: false :: Y))))) p [false, true, true, false, false, true, true, true, true, false, false, false, false, true, true, false] false) = some (.T2 [true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false] (false :: dbl (true :: sx true ((sx true (sx true (sx true (false :: false :: Y))))).tail)) q [true, true, false, false, true, true, true, true, false, false, false, false, true, true, false] false) := by
  refine ⟨bne p (par false (dbl (true :: ((sx true (sx true (sx true (false :: false :: Y))))).tail))), ?_⟩
  show coreO [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false] (dbl (true :: ((sx true (sx true (sx true (false :: false :: Y))))).tail)) p (true :: [false, true, true, false, false, true, true, true, true, false, false, false, false, true, true, false]) false = _
  rw [core_even _ _ _ _ _ rfl]
  rfl

theorem w43_step6 (Y : List Bool) (p : Bool) :
    ∃ q, astep (.T2 [true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false] (false :: dbl (true :: sx true ((sx true (sx true (sx true (false :: false :: Y))))).tail)) p [true, true, false, false, true, true, true, true, false, false, false, false, true, true, false] false) = some (.T2 [true, false, true, false, true] (false :: false :: dbl (sx true ((sx true (sx true (sx true (false :: false :: Y))))).tail)) q [false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, true, true, false, false, false, false, true, true, false] false) := by
  refine ⟨p, ?_⟩
  show coreO [true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, false] (dbl (true :: (sx true ((sx true (sx true (sx true (false :: false :: Y))))).tail))) p (true :: [true, true, false, false, true, true, true, true, false, false, false, false, true, true, false]) false = _
  rw [core_odd _ _ _ _ _ rfl]
  rfl

/-- **The window after list step 28,450 is safe** for every far part starting `u v v`: six list steps, the last of
which leaves a witness. -/
theorem window_W43 (Y : List Bool) (p : Bool) : SafeWithin 6 (.EO W43 (some (dbl (true :: false :: false :: Y))) p) := by
  obtain ⟨q1, h1⟩ := w43_step1 Y p
  obtain ⟨q2, h2⟩ := w43_step2 Y q1
  obtain ⟨q3, h3⟩ := w43_step3 Y q2
  obtain ⟨q4, h4⟩ := w43_step4 Y q3
  obtain ⟨q5, h5⟩ := w43_step5 Y q4
  obtain ⟨q6, h6⟩ := w43_step6 Y q5
  exact safeWithin_of_step _ _ _ h1 (safeWithin_of_step _ _ _ h2 (safeWithin_of_step _ _ _ h3 (safeWithin_of_step _ _ _ h4 (safeWithin_of_step _ _ _ h5 (safeWithin_of_step _ _ _ h6 (safeWithin_of_safe 0 _ (Or.inr ⟨⟨2, _, rfl⟩, [false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false], 1, [false, false, true, true, true, true, false, false, false, false, true, true, false], by simp, rfl⟩)))))))

end H75625
