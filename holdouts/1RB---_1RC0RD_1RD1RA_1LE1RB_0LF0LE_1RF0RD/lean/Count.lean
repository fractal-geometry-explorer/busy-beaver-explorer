import Rules

/-!
# The event rule of 1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD, for every size

Two counters share the tape.  Left of the head, a bit string `bs` (lowest bit nearest the head) is written in pairs
`1 b` (`enc`): reading left to right, `... b2 1 b1 1 b0 1`.  Right of the head, a binary counter `ds` (lowest digit
first) is written in groups of three cells `0 0 d` (`ctr`).

* `count`: one *count*.  `enc (0 :: b1 :: hi) L  B>  ctr ds R` reaches `enc (0 :: b1 :: inc hi) L  B>  ctr (inc ds) R`
  whenever both increments stay inside their strings (`false ∈ hi`, `false ∈ ds`).  So every count adds 1 to the
  right counter and 4 to the left string (its two lowest bits are left alone).
* `iter`: `2^d` counts, by induction on `d`: with `d` counter digits that are 0 below `ds`, and `lo` (of length `d`)
  the bits just above `b1`, the left string `lo ++ h` becomes `lo ++ inc h`: `2^d · 4` was added.
* `event_rule`: right after an event, `P d bs` (the counter `0^d 1`, the rest of the tape blank) reaches
  `P (d+1) bs'` with `bs' = bs + 2^(d+1)`, written as lists: `b1 :: lo ++ h` becomes `b1 :: lo ++ inc h` with
  `lo` of length `d`, whenever `false ∈ h` (the addition does not carry out of the top bit).
* `event_to_P`: an event in the README's sense, `bits 0 1^(3d+4) B>0` with the bits `b1 :: hi`, reaches
  `P (d+1) (b1 :: inc hi)` when `false ∈ hi`.

The step counts are not stated (`Reach`).  All rules hold for every left context `L` (in the run, `1 1` and blank).
-/

namespace H140108

open TM

/-- `a` reaches `b` in some number of steps. -/
def Reach (a b : Cfg St) : Prop := ∃ t, steps t a = some b

theorem Reach.trans' {a b c : Cfg St} (h1 : Reach a b) (h2 : Reach b c) : Reach a c := by
  obtain ⟨t1, h1⟩ := h1
  obtain ⟨t2, h2⟩ := h2
  exact ⟨t1 + t2, TM.steps_seq trans h1 h2⟩

theorem Reach.refl' (a : Cfg St) : Reach a a := ⟨0, rfl⟩

theorem reach_of {t : Nat} {a b : Cfg St} (h : steps t a = some b) : Reach a b := ⟨t, h⟩

/-- A bit string in pairs, lowest bit nearest the head: `enc [b0, b1, ...] L` is `L ... 1 b1 1 b0 1` read leftwards
as `1 b0 1 b1 ... L`. -/
def enc : List Bool → Tape → Tape
  | [], L => L
  | b :: bs, L => cons true (cons b (enc bs L))

/-- A counter in groups `0 0 d`, lowest digit nearest the head. -/
def ctr : List Bool → Tape → Tape
  | [], R => R
  | d :: ds, R => cons false (cons false (cons d (ctr ds R)))

/-- Binary increment of a list, lowest bit first (the empty list, an overflow, is left empty). -/
def inc : List Bool → List Bool
  | [] => []
  | false :: l => true :: l
  | true :: l => false :: inc l

theorem inc_split : ∀ (l : List Bool), false ∈ l →
    ∃ r rest, l = List.replicate r true ++ false :: rest ∧ inc l = List.replicate r false ++ true :: rest
  | [], h => by simp at h
  | false :: l, _ => ⟨0, l, rfl, rfl⟩
  | true :: l, h => by
    have h' : false ∈ l := by simpa using h
    obtain ⟨r, rest, e1, e2⟩ := inc_split l h'
    exact ⟨r + 1, rest, by rw [e1]; rfl, by show false :: inc l = _; rw [e2]; rfl⟩

theorem enc_trues (r : Nat) (l : List Bool) (L : Tape) :
    enc (List.replicate r true ++ l) L = rep r [true, true] (enc l L) := by
  induction r with
  | zero => rfl
  | succ r ih => show cons true (cons true (enc (List.replicate r true ++ l) L)) = _; rw [ih]; rfl

theorem enc_falses (r : Nat) (l : List Bool) (L : Tape) :
    enc (List.replicate r false ++ l) L = rep r [true, false] (enc l L) := by
  induction r with
  | zero => rfl
  | succ r ih => show cons true (cons false (enc (List.replicate r false ++ l) L)) = _; rw [ih]; rfl

theorem ctr_ones (t : Nat) (l : List Bool) (R : Tape) :
    ctr (List.replicate t true ++ l) R = rep t [false, false, true] (ctr l R) := by
  induction t with
  | zero => rfl
  | succ t ih => show cons false (cons false (cons true (ctr (List.replicate t true ++ l) R))) = _; rw [ih]; rfl

theorem ctr_zeros (t : Nat) (l : List Bool) (R : Tape) :
    ctr (List.replicate t false ++ l) R = rep t [false, false, false] (ctr l R) := by
  induction t with
  | zero => rfl
  | succ t ih => show cons false (cons false (cons false (ctr (List.replicate t false ++ l) R))) = _; rw [ih]; rfl

theorem rep_one_comm (b : Bool) (n : Nat) (s : Tape) : rep n [b] (cons b s) = cons b (rep n [b] s) := by
  induction n with
  | zero => rfl
  | succ n ih => show cons b (rep n [b] (cons b s)) = cons b (cons b (rep n [b] s)); rw [ih]

theorem rep_two (b : Bool) (n : Nat) (s : Tape) : rep n [b, b] s = rep (2 * n) [b] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, rep_succ, ih]
    show cons b (cons b (rep (2 * n) [b] s)) = cons b (rep (2 * n + 1) [b] s)
    rfl

theorem rep_three (b : Bool) (n : Nat) (s : Tape) : rep n [b, b, b] s = rep (3 * n) [b] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by omega, rep_succ, ih]
    show cons b (cons b (cons b (rep (3 * n) [b] s))) = cons b (rep (3 * n + 1 + 1) [b] s)
    rw [rep_succ, rep_succ]
    show cons b (cons b (cons b (rep (3 * n) [b] s))) = cons b (cons b (cons b (rep (3 * n) [b] s)))
    rfl

/-- `L B> (0 0 1)^t` (the counter's lowest `t` digits, all 1) becomes `L 1^(3t) B>`. -/
theorem carry (t : Nat) : ∀ (ds : List Bool) (L R : Tape),
    Reach ⟨L, ctr (List.replicate t true ++ ds) R, .B⟩ ⟨rep (3 * t) [true] L, ctr ds R, .B⟩ := by
  intro ds L R
  rw [ctr_ones, ← rep_three]
  have c0 : ∀ L R : Tape, steps 3 ⟨app [] L, app [false, false, true] R, .B⟩
      = some ⟨app [] (app [true, true, true] L), R, .B⟩ := fun _ _ => rfl
  exact reach_of (cross_r trans c0 t L (ctr ds R))

/-- After the carry, the counter digit 0 becomes 1 and E erases back to the separator `b0 = 0`. -/
theorem erase_phase (t : Nat) (b1 : Bool) (hi ds : List Bool) (L R : Tape) :
    Reach ⟨rep (3 * t) [true] (enc (false :: b1 :: hi) L), ctr (false :: ds) R, .B⟩
      ⟨enc (b1 :: hi) L, cons false (cons false (ctr (List.replicate t false ++ true :: ds) R)), .E⟩ := by
  have h1 : steps 3 ⟨rep (3 * t) [true] (enc (false :: b1 :: hi) L), ctr (false :: ds) R, .B⟩
      = some ⟨cons true (rep (3 * t) [true] (enc (false :: b1 :: hi) L)),
          cons true (cons true (ctr ds R)), .E⟩ := rfl
  refine Reach.trans' (reach_of h1) ?_
  have e : cons true (rep (3 * t) [true] (enc (false :: b1 :: hi) L))
      = rep (3 * t + 2) [true] (cons false (enc (b1 :: hi) L)) := by
    show cons true (rep (3 * t) [true] (cons true (cons false (enc (b1 :: hi) L)))) = _
    rw [rep_one_comm]; rfl
  rw [e]
  have h2 := erase (3 * t + 2) (enc (b1 :: hi) L) (cons true (ctr ds R))
  refine Reach.trans' (reach_of h2) ?_
  rw [ctr_zeros, rep_three, show 3 * t + 2 = (3 * t + 1) + 1 by omega, rep_succ, rep_succ]
  show Reach ⟨_, cons false (cons false (cons false (cons false (rep (3 * t) [false] (cons true (ctr ds R)))))), _⟩ _
  rw [← rep_one_comm, ← rep_one_comm]
  exact Reach.refl' _

/-- The left increment when `b1 = 0`. -/
theorem walk_false (r : Nat) (hrest : List Bool) (L Z : Tape) :
    Reach ⟨enc (false :: (List.replicate r true ++ false :: hrest)) L, cons false (cons false Z), .E⟩
      ⟨enc (List.replicate (r + 2) false ++ true :: hrest) L, Z, .B⟩ := by
  have h1 : steps 11 ⟨enc (false :: (List.replicate r true ++ false :: hrest)) L, cons false (cons false Z), .E⟩
      = some ⟨cons true (enc (List.replicate r true ++ false :: hrest) L), cons false (cons true (cons true Z)), .E⟩ :=
    rfl
  refine Reach.trans' (reach_of h1) ?_
  have e : cons true (enc (List.replicate r true ++ false :: hrest) L)
      = rep (2 * r + 2) [true] (cons false (enc hrest L)) := by
    rw [enc_trues, rep_two]
    show cons true (rep (2 * r) [true] (cons true (cons false (enc hrest L)))) = _
    rw [rep_one_comm]; rfl
  rw [e]
  refine Reach.trans' (reach_of (shift (2 * r + 2) (cons false (enc hrest L)) (cons true (cons true Z)))) ?_
  rw [rep_one_comm, rep_one_comm]
  have h3 : steps 4 ⟨cons false (enc hrest L), cons false (cons true (cons true (rep (2 * r + 2) [true] Z))), .E⟩
      = some ⟨cons false (cons true (cons true (enc hrest L))), cons true (rep (2 * r + 2) [true] Z), .D⟩ := rfl
  refine Reach.trans' (reach_of h3) ?_
  rw [← rep_one_comm, show 2 * r + 2 = 2 * (r + 1) by omega, ← rep_two, show cons true Z = app [true] Z from rfl]
  refine Reach.trans' (reach_of (pairs (r + 1) _ _)) ?_
  have h4 : steps 1 ⟨rep (r + 1) [false, true] (cons false (cons true (cons true (enc hrest L)))), app [true] Z, .D⟩
      = some ⟨cons true (rep (r + 1) [false, true] (cons false (cons true (cons true (enc hrest L))))), Z, .B⟩ := rfl
  refine Reach.trans' (reach_of h4) ?_
  have e2 : cons true (rep (r + 1) [false, true] (cons false (cons true (cons true (enc hrest L)))))
      = enc (List.replicate (r + 2) false ++ true :: hrest) L := by
    rw [enc_falses]
    have hr := rep_rotate (r + 1) [true] [false, true] [true, false] rfl (cons false (cons true (cons true (enc hrest L))))
    calc cons true (rep (r + 1) [false, true] (cons false (cons true (cons true (enc hrest L)))))
        = app [true] (rep (r + 1) [false, true] (cons false (cons true (cons true (enc hrest L))))) := rfl
      _ = rep (r + 1) [true, false] (app [true] (cons false (cons true (cons true (enc hrest L))))) := hr
      _ = rep (r + 1) [true, false] (app [true, false] (enc (true :: hrest) L)) := rfl
      _ = rep (r + 2) [true, false] (enc (true :: hrest) L) := rep_app_comm _ _ _
  rw [e2]
  exact Reach.refl' _

/-- The left increment when `b1 = 1`. -/
theorem walk_true (r : Nat) (hrest : List Bool) (L Z : Tape) :
    Reach ⟨enc (true :: (List.replicate r true ++ false :: hrest)) L, cons false (cons false Z), .E⟩
      ⟨enc (false :: true :: (List.replicate r false ++ true :: hrest)) L, Z, .B⟩ := by
  have e : enc (true :: (List.replicate r true ++ false :: hrest)) L
      = rep (2 * r + 3) [true] (cons false (enc hrest L)) := by
    show cons true (cons true (enc (List.replicate r true ++ false :: hrest) L)) = _
    rw [enc_trues, rep_two]
    show cons true (cons true (rep (2 * r) [true] (cons true (cons false (enc hrest L))))) = _
    rw [rep_one_comm]; rfl
  rw [e]
  refine Reach.trans' (reach_of (shift (2 * r + 3) (cons false (enc hrest L)) (cons false Z))) ?_
  rw [show 2 * r + 3 = (2 * r + 2) + 1 by omega, rep_succ]
  have h3 : steps 4 ⟨cons false (enc hrest L), cons false (app [true] (rep (2 * r + 2) [true] (cons false Z))), .E⟩
      = some ⟨cons false (cons true (cons true (enc hrest L))), rep (2 * r + 2) [true] (cons false Z), .D⟩ := rfl
  refine Reach.trans' (reach_of h3) ?_
  rw [show 2 * r + 2 = 2 * (r + 1) by omega, ← rep_two]
  refine Reach.trans' (reach_of (pairs (r + 1) _ _)) ?_
  -- `rep (r+1) [0,1] Y` with `Y = 0 1 1 enc hrest`, the head on `0 Z`
  have h4 : ∀ X : Tape, steps 4 ⟨rep (r + 1) [false, true] X, cons false Z, .D⟩
      = some ⟨rep r [false, true] X, cons false (cons true (cons true Z)), .E⟩ := fun _ => rfl
  refine Reach.trans' (reach_of (h4 _)) ?_
  have hr := rep_rotate r [false] [true, false] [false, true] rfl (cons true (cons true (enc hrest L)))
  rw [show cons false (cons true (cons true (enc hrest L))) = app [false] (cons true (cons true (enc hrest L))) from rfl,
    ← hr]
  have h5 : ∀ X : Tape, steps 5 ⟨app [false] X, cons false (cons true (cons true Z)), .E⟩
      = some ⟨cons true (cons false (cons true (cons true X))), Z, .B⟩ := fun _ => rfl
  refine Reach.trans' (reach_of (h5 _)) ?_
  show Reach _ ⟨cons true (cons false (cons true (cons true (enc (List.replicate r false ++ true :: hrest) L)))), Z, .B⟩
  rw [enc_falses]
  exact Reach.refl' _

/-- **One count.** `enc (0 :: b1 :: hi) L B> ctr ds R` reaches `enc (0 :: b1 :: inc hi) L B> ctr (inc ds) R`. -/
theorem count (b1 : Bool) (hi ds : List Bool) (hh : false ∈ hi) (hd : false ∈ ds) (L R : Tape) :
    Reach ⟨enc (false :: b1 :: hi) L, ctr ds R, .B⟩ ⟨enc (false :: b1 :: inc hi) L, ctr (inc ds) R, .B⟩ := by
  obtain ⟨t, ds', e1, e2⟩ := inc_split ds hd
  obtain ⟨r, hrest, e3, e4⟩ := inc_split hi hh
  rw [e2, e1]
  refine Reach.trans' (carry t (false :: ds') _ R) ?_
  refine Reach.trans' (erase_phase t b1 hi ds' L R) ?_
  rw [e4, e3]
  cases b1 with
  | false => exact walk_false r hrest L _
  | true => exact walk_true r hrest L _

theorem false_mem_inc : ∀ (l : List Bool), false ∈ l → ∀ a : Bool, false ∈ inc (a :: l)
  | l, h, false => by simpa [inc] using h
  | _, _, true => by simp [inc]

theorem inc_inc (a : Bool) (l : List Bool) : inc (inc (a :: l)) = a :: inc l := by
  cases a <;> rfl

/-- **`2^d` counts.** With the counter's lowest `d` digits 0 and `lo` (length `d`) above `b1`, the left string
`lo ++ h` becomes `lo ++ inc h` and the counter part `ds` above the `d` zeros becomes `inc ds`. -/
theorem iter (b1 : Bool) (L R : Tape) (d : Nat) : ∀ (lo h ds : List Bool), lo.length = d → false ∈ h → false ∈ ds →
    Reach ⟨enc (false :: b1 :: (lo ++ h)) L, ctr (List.replicate d false ++ ds) R, .B⟩
      ⟨enc (false :: b1 :: (lo ++ inc h)) L, ctr (List.replicate d false ++ inc ds) R, .B⟩ := by
  induction d with
  | zero =>
    intro lo h ds hl hh hd
    rw [List.length_eq_zero_iff.mp hl]
    exact count b1 h ds hh hd L R
  | succ d ih =>
    intro lo h ds hl hh hd
    have hne : lo ≠ [] := by intro e; rw [e] at hl; simp at hl
    have hl1 : lo.dropLast.length = d := by rw [List.length_dropLast, hl]; rfl
    rw [← List.dropLast_concat_getLast hne]
    generalize lo.dropLast = lo1 at hl1
    generalize lo.getLast hne = a
    have e1 : lo1 ++ [a] ++ h = lo1 ++ a :: h := by simp
    have e2 : List.replicate (d + 1) false ++ ds = List.replicate d false ++ false :: ds := by
      simp [List.replicate_succ']
    have e3 : List.replicate (d + 1) false ++ inc ds = List.replicate d false ++ inc (inc (false :: ds)) := by
      simp [List.replicate_succ', inc]
    have e4 : lo1 ++ [a] ++ inc h = lo1 ++ inc (inc (a :: h)) := by simp [inc_inc]
    rw [e1, e2, e3, e4]
    have s1 := ih lo1 (a :: h) (false :: ds) hl1 (List.mem_cons_of_mem _ hh) List.mem_cons_self
    refine Reach.trans' s1 ?_
    exact ih lo1 (inc (a :: h)) (true :: ds) hl1 (false_mem_inc h hh a) (List.mem_cons_of_mem _ hd)

/-- The moment right after an event: the counter `0^d 1`, blank to its right; the bits `bs` (event form) left of
the pair `0 1` the head has just left. -/
def P (d : Nat) (bs : List Bool) (L : Tape) : Cfg St :=
  ⟨enc (false :: bs) L, ctr (List.replicate d false ++ [true]) blank, .B⟩

theorem ctr_blank (ds : List Bool) : ctr (ds ++ [false]) blank = ctr ds blank := by
  induction ds with
  | nil => show cons false (cons false (cons false blank)) = blank; rw [cons_false_blank, cons_false_blank, cons_false_blank]
  | cons d ds ih => show cons false (cons false (cons d (ctr (ds ++ [false]) blank))) = _; rw [ih]; rfl

/-- **The event rule, for every size.** `P d (b1 :: lo ++ h)` reaches `P (d+1) (b1 :: lo ++ inc h)` when `lo`
has `d` bits and `false ∈ h`: the bit string (lowest bit `b1`) gains `2^(d+1)`, carried within the string. -/
theorem event_rule (d : Nat) (b1 : Bool) (lo h : List Bool) (hl : lo.length = d) (hh : false ∈ h) (L : Tape) :
    Reach (P d (b1 :: (lo ++ h)) L) (P (d + 1) (b1 :: (lo ++ inc h)) L) := by
  unfold P
  rw [← ctr_blank (List.replicate d false ++ [true]),
    show List.replicate d false ++ [true] ++ [false] = List.replicate d false ++ [true, false] by simp,
    show List.replicate (d + 1) false ++ [true] = List.replicate d false ++ inc [true, false] by
      simp [inc, List.replicate_succ']]
  exact iter b1 L blank d lo h [true, false] hl hh (by simp)

/-- An event in the README's sense, `L bits 0 1^(3d+4) B>0` (the bits `b1 :: hi`, blank to the right), reaches
`P (d+1) (b1 :: inc hi)` when `false ∈ hi`. -/
theorem event_to_P (d : Nat) (b1 : Bool) (hi : List Bool) (hh : false ∈ hi) (L : Tape) :
    Reach ⟨rep (3 * d + 4) [true] (cons false (enc (b1 :: hi) L)), blank, .B⟩ (P (d + 1) (b1 :: inc hi) L) := by
  have e : rep (3 * d + 4) [true] (cons false (enc (b1 :: hi) L))
      = rep (3 * (d + 1)) [true] (enc (false :: b1 :: hi) L) := by
    rw [show 3 * d + 4 = 3 * (d + 1) + 1 by omega, rep_add]
    rfl
  rw [e, show (blank : Tape) = ctr (false :: []) blank from (ctr_blank []).symm]
  refine Reach.trans' (erase_phase (d + 1) b1 hi [] L blank) ?_
  obtain ⟨r, hrest, e3, e4⟩ := inc_split hi hh
  unfold P
  rw [e4, e3]
  cases b1 with
  | false =>
    exact walk_false r hrest L (ctr (List.replicate (d + 1) false ++ [true]) blank)
  | true => exact walk_true r hrest L _

end H140108

namespace H140108

open TM

/-- The run from blank tape reaches the first post-event configuration `P 0 [0, 1]` (bits `10`, lowest first `01`)
after 69 steps, with `1 1` and blank left of the string. -/
theorem blank_to_P : steps 69 init = some (P 0 [false, true] (cons true (cons true blank))) := by
  have h : TM.fsteps trans 69 (FCfg.blank .A)
      = some (⟨[true, false, true, false, true, true, true, true], [false, false, true], .B⟩ : FCfg St) := by
    decide +kernel
  show TM.steps trans 69 (FCfg.blank St.A).toCfg = _
  rw [FCfg.steps_eq, h]
  rfl

end H140108
