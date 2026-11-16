import Rules
import VisitRules

/-!
# The visit map of 1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA

The tape is a list of runs of ones separated by single 0s; a *visit* is the configuration `V l` with B on the blank
cell left of the runs `l`.  `visit l` is the list at the next visit, or `none` when every run of `l` (the first one
after adding 2) is even: then E runs to the right end and F reads a 0 there.  `visit_step` proves this for every list
of the domain `D`, which the map preserves; the run from blank tape enters `D` at step 423 (`blank_to_V`), so
`halts_iff`: the machine halts from blank tape iff the orbit of `l0` under `visit` reaches `none`.
(The Python mirror of these definitions is `py/visit.py`.)
-/

namespace H175628

open TM

/-! ## Tapes of runs -/

/-- Runs of ones to the right, each followed by one 0, then blank tape. -/
def runsR : List Nat → Tape
  | [] => blank
  | r :: l => rep r [true] (cons false (runsR l))

/-- Even runs to the left, given by their half-lengths, nearest first, each followed by one 0. -/
def evL : List Nat → Tape
  | [] => blank
  | h :: hs => rep h [true, true] (cons false (evL hs))

/-- A visit of the left end: B on the blank cell just left of the runs `l`. -/
def V (l : List Nat) : Config := ⟨blank, cons false (runsR l), .B⟩

theorem pairs (n : Nat) (s : Tape) : rep n [true, true] s = rep (2 * n) [true] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show cons true (cons true (rep n [true, true] s)) = cons true (cons true (rep (2 * n) [true] s))
    rw [ih]

theorem c1 (s : Tape) : cons true s = rep 1 [true] s := rfl

theorem ones_add (a b : Nat) (s : Tape) : rep a [true] (rep b [true] s) = rep (a + b) [true] s :=
  (rep_add a b [true] s).symm

theorem ones_congr {a b : Nat} (h : a = b) (s : Tape) : rep a [true] s = rep b [true] s := by rw [h]

theorem units_tape (t : Nat) (l : List Nat) :
    rep t [true, false] (runsR l) = runsR (List.replicate t 1 ++ l) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show cons true (cons false (rep t [true, false] (runsR l))) = _
    rw [ih]; rfl

theorem alt_shift (t : Nat) (s : Tape) :
    cons true (rep t [false, true] (cons false s)) = rep (t + 1) [true, false] s := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show cons true (cons false (cons true (rep t [false, true] (cons false s)))) =
      cons true (cons false (rep (t + 1) [true, false] s))
    rw [ih]

/-- A run of at least zero steps. -/
def Reach (c c' : Config) : Prop := ∃ n, steps n c = some c'

theorem Reach.trans {a b c : Config} (h₁ : Reach a b) (h₂ : Reach b c) : Reach a c := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  exact ⟨n₁ + n₂, steps_seq H175628.trans h₁ h₂⟩

theorem Reach.of {n : Nat} {c c' : Config} (h : steps n c = some c') : Reach c c' := ⟨n, h⟩

/-! ## The visit map on lists of runs -/

/-- C on the 0 before the runs `l` (which start with a unit), the even runs `hs` to its left. -/
def cascC : List Nat → List Nat → List Nat
  | [], l => 6 :: 4 :: l.drop 5
  | [c], l => (2 * c + 3 + l.getD 1 1) :: l.drop 2
  | c :: t :: hs, l => cascC hs (List.replicate t 1 ++ (2 * c + 4 + l.getD 1 1) :: l.drop 2)

/-- B on the 0 before the runs `l`, the even runs `hs` to its left. -/
def cascB : List Nat → List Nat → List Nat
  | t :: hs, w :: l => cascC hs (List.replicate t 1 ++ (w + 1) :: l)
  | _, l => l

/-- E scanning to the right over even runs (half-lengths collected in `hs`) up to the first odd run. -/
def scan : List Nat → List Nat → Option (List Nat)
  | _, [] => none
  | hs, r :: l =>
    if r % 2 = 0 then scan ((r / 2) :: hs) l
    else match l with
      | [] => some (cascC hs (List.replicate ((r + 1) / 2) 1 ++ [1]))
      | r1 :: rest => some (cascB hs ((r + r1 + 1) :: rest))

/-- One visit of the left end; `none`: the machine halts. -/
def visit : List Nat → Option (List Nat)
  | [] => none
  | x :: l => scan [(x + 2) / 2] l

/-- The last (farthest) half-length is at least 7. -/
def lastGe : List Nat → Prop
  | [] => True
  | [x] => 7 ≤ x
  | _ :: y :: hs => lastGe (y :: hs)

theorem lastGe_tail : ∀ (x : Nat) (hs : List Nat), lastGe (x :: hs) → lastGe hs
  | _, [], _ => trivial
  | _, _ :: _, h => h

theorem lastGe_cons : ∀ (x y : Nat) (hs : List Nat), lastGe (y :: hs) → lastGe (x :: y :: hs) :=
  fun _ _ _ h => h

/-! ## The machine follows the map -/

theorem stage_tape (c w : Nat) (X : Tape) :
    cons true (rep c [true, true] (cons true (cons true (cons true (cons true (cons true (rep w [true] X))))))) =
      rep (2 * (c + 1) + 3 + (w + 1)) [true] X := by
  simp only [pairs, c1, ones_add]
  exact ones_congr (by omega) X

theorem cascC_sound : ∀ (hs l : List Nat), (∀ h ∈ hs, 1 ≤ h) → lastGe hs →
    (hs = [] → ∃ l', l = 1 :: 1 :: 1 :: 1 :: 1 :: l') → (∃ w l', l = 1 :: (w + 1) :: l') →
    Reach ⟨evL hs, cons false (runsR l), .C⟩ (V (cascC hs l))
  | [], l, _, _, h5, _ => by
    obtain ⟨l', rfl⟩ := h5 rfl
    exact ⟨44, left_end (runsR l')⟩
  | [c], l, hp, _, _, hl => by
    obtain ⟨w, l', rfl⟩ := hl
    have hc : 1 ≤ c := hp c (by simp)
    obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have h := stage c blank (rep w [true] (cons false (runsR l')))
    rw [stage_tape] at h
    exact ⟨_, h⟩
  | c :: t :: hs, l, hp, hok, _, hl => by
    obtain ⟨w, l', rfl⟩ := hl
    have hc : 1 ≤ c := hp c (by simp)
    have ht : 1 ≤ t := hp t (by simp)
    obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have h₁ := stage c (evL ((t + 1) :: hs)) (rep w [true] (cons false (runsR l')))
    rw [stage_tape] at h₁
    have h₂ := fillzig t (evL hs) (rep (2 * (c + 1) + 3 + (w + 1)) [true] (cons false (runsR l')))
    rw [alt_shift] at h₂
    have e : cons true (rep (2 * (c + 1) + 3 + (w + 1)) [true] (cons false (runsR l'))) =
        runsR ((2 * (c + 1) + 4 + (w + 1)) :: l') :=
      ones_congr (a := 2 * (c + 1) + 3 + (w + 1) + 1) (by omega) _
    rw [e, units_tape] at h₂
    have hrec := cascC_sound hs (List.replicate (t + 1) 1 ++ (2 * (c + 1) + 4 + (w + 1)) :: l')
      (fun h hh => hp h (by simp [hh])) (lastGe_tail _ _ (lastGe_tail _ _ hok))
      (by
        intro e0; subst e0
        have h7 : 7 ≤ t + 1 := hok
        obtain ⟨k, rfl⟩ : ∃ k, t = k + 4 := ⟨t - 4, by omega⟩
        exact ⟨_, rfl⟩)
      (by
        cases t with
        | zero => exact ⟨_, _, rfl⟩
        | succ t => exact ⟨0, _, rfl⟩)
    exact (Reach.of h₁).trans ((Reach.of h₂).trans hrec)

theorem cascB_sound : ∀ (hs : List Nat) (w : Nat) (l : List Nat), (∀ h ∈ hs, 1 ≤ h) → lastGe hs →
    Reach ⟨evL hs, cons false (runsR (w :: l)), .B⟩ (V (cascB hs (w :: l)))
  | [], w, l, _, _ => ⟨0, rfl⟩
  | t :: hs, w, l, hp, hok => by
    have ht : 1 ≤ t := hp t (by simp)
    obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have h₂ := fillzig t (evL hs) (runsR (w :: l))
    rw [alt_shift] at h₂
    have e : cons true (runsR (w :: l)) = runsR ((w + 1) :: l) := rfl
    rw [e, units_tape] at h₂
    have hrec := cascC_sound hs (List.replicate (t + 1) 1 ++ (w + 1) :: l)
      (fun h hh => hp h (by simp [hh])) (lastGe_tail _ _ hok)
      (by
        intro e0; subst e0
        have h7 : 7 ≤ t + 1 := hok
        obtain ⟨k, rfl⟩ : ∃ k, t = k + 4 := ⟨t - 4, by omega⟩
        exact ⟨_, rfl⟩)
      (by
        cases t with
        | zero => exact ⟨_, _, rfl⟩
        | succ t => exact ⟨0, _, rfl⟩)
    exact (Reach.of h₂).trans hrec

theorem evL_cons_add (a c : Nat) (hs : List Nat) :
    rep a [true, true] (rep c [true, true] (cons false (evL hs))) = evL ((c + a) :: hs) := by
  show _ = rep (c + a) [true, true] (cons false (evL hs))
  rw [Nat.add_comm c a, rep_add]

theorem even_run (b : Nat) (X : Tape) :
    rep (2 * (b + 1)) [true] X = cons true (cons true (rep b [true, true] X)) := by
  rw [pairs]; rfl

theorem odd_run (b : Nat) (X : Tape) : rep (2 * b + 1) [true] X = cons true (rep b [true, true] X) := by
  rw [pairs]; rfl

theorem odd_tape (b r1 : Nat) (Z : Tape) :
    cons true (cons true (rep b [true, true] (cons true (rep r1 [true] Z)))) =
      rep (2 * b + 1 + (r1 + 1) + 1) [true] Z := by
  simp only [pairs, c1, ones_add]
  exact ones_congr (by omega) Z

/-- The scan: from E inside an even run (half-length `c + a`, `a` pairs still ahead), the machine reaches the visit
that `scan` computes, or halts if `scan` says so. -/
theorem scan_sound : ∀ (l hs : List Nat) (c a : Nat), 1 ≤ c + a → (∀ r ∈ l, 1 ≤ r) → (∀ h ∈ hs, 1 ≤ h) →
    lastGe ((c + a) :: hs) →
    (∀ l', scan ((c + a) :: hs) l = some l' →
      Reach ⟨rep c [true, true] (cons false (evL hs)), rep a [true, true] (cons false (runsR l)), .E⟩ (V l')) ∧
    (scan ((c + a) :: hs) l = none →
      ∃ n c', steps n ⟨rep c [true, true] (cons false (evL hs)), rep a [true, true] (cons false (runsR l)), .E⟩
        = some c' ∧ step c' = none)
  | [], hs, c, a, _, _, _, _ => by
    refine ⟨fun l' h => by simp [scan] at h, fun _ => ?_⟩
    have h := scan_halt a (rep c [true, true] (cons false (evL hs))) blank
    simp only [cons_false_blank] at h
    have e0 : cons false (runsR []) = blank := cons_false_blank
    rw [e0]
    refine ⟨_, _, h, ?_⟩
    rfl
  | r :: l, hs, c, a, hca, hl, hp, hok => by
    have hr : 1 ≤ r := hl r (by simp)
    have hl' : ∀ r ∈ l, 1 ≤ r := fun x hx => hl x (by simp [hx])
    have hp' : ∀ h ∈ (c + a) :: hs, 1 ≤ h := by
      intro h hh
      rcases List.mem_cons.1 hh with rfl | hh
      · exact hca
      · exact hp h hh
    by_cases hev : r % 2 = 0
    · obtain ⟨b, rfl⟩ : ∃ b, r = 2 * (b + 1) := ⟨r / 2 - 1, by omega⟩
      have e2 : 2 * (b + 1) / 2 = 1 + b := by omega
      have hs1 : scan ((c + a) :: hs) (2 * (b + 1) :: l) = scan ((1 + b) :: (c + a) :: hs) l := by
        simp [scan, e2]
      have ih := scan_sound l ((c + a) :: hs) 1 b (by omega) hl' hp' hok
      have h := scan_even a (rep c [true, true] (cons false (evL hs))) (rep b [true, true] (cons false (runsR l)))
      rw [evL_cons_add] at h
      have e : rep a [true, true] (cons false (runsR (2 * (b + 1) :: l))) =
          rep a [true, true] (cons false (cons true (cons true (rep b [true, true] (cons false (runsR l)))))) := by
        show rep a [true, true] (cons false (rep (2 * (b + 1)) [true] (cons false (runsR l)))) = _
        rw [even_run]
      rw [hs1, e]
      refine ⟨fun l' h' => (Reach.of h).trans (ih.1 l' h'), fun h' => ?_⟩
      obtain ⟨n, c', hn, hc'⟩ := ih.2 h'
      exact ⟨_, c', steps_seq H175628.trans h hn, hc'⟩
    · obtain ⟨b, rfl⟩ : ∃ b, r = 2 * b + 1 := ⟨r / 2, by omega⟩
      cases l with
      | nil =>
        have e2 : (2 * b + 1 + 1) / 2 = b + 1 := by omega
        have hs1 : scan ((c + a) :: hs) [2 * b + 1] =
            some (cascC ((c + a) :: hs) (List.replicate (b + 1) 1 ++ [1])) := by
          simp [scan, e2]
        rw [hs1]
        refine ⟨fun l' h' => ?_, fun h' => by cases h'⟩
        cases h'
        have h := scan_last a b (rep c [true, true] (cons false (evL hs))) blank
        rw [evL_cons_add] at h
        simp only [cons_false_blank] at h
        have e : rep a [true, true] (cons false (runsR [2 * b + 1])) =
            rep a [true, true] (cons false (cons true (rep b [true, true] blank))) := by
          show rep a [true, true] (cons false (rep (2 * b + 1) [true] (cons false blank))) = _
          rw [odd_run, cons_false_blank]
        have e' : cons true (cons false (rep b [true, false] (cons true blank))) =
            runsR (List.replicate (b + 1) 1 ++ [1]) := by
          rw [← units_tape]
          show _ = cons true (cons false (rep b [true, false] (cons true (cons false blank))))
          rw [cons_false_blank]
        rw [e]; rw [e'] at h
        have hrec := cascC_sound ((c + a) :: hs) (List.replicate (b + 1) 1 ++ [1]) hp' hok
          (by intro e0; cases e0)
          (by
            cases b with
            | zero => exact ⟨0, _, rfl⟩
            | succ b => exact ⟨0, _, rfl⟩)
        exact (Reach.of h).trans hrec
      | cons r1 rest =>
        have hr1 : 1 ≤ r1 := hl' r1 (by simp)
        obtain ⟨r1, rfl⟩ : ∃ r1', r1 = r1' + 1 := ⟨r1 - 1, by omega⟩
        have hs1 : scan ((c + a) :: hs) ((2 * b + 1) :: (r1 + 1) :: rest) =
            some (cascB ((c + a) :: hs) ((2 * b + 1 + (r1 + 1) + 1) :: rest)) := by
          simp [scan]
        rw [hs1]
        refine ⟨fun l' h' => ?_, fun h' => by cases h'⟩
        cases h'
        have h := scan_odd a b (rep c [true, true] (cons false (evL hs))) (rep r1 [true] (cons false (runsR rest)))
        rw [evL_cons_add, odd_tape] at h
        have e : rep a [true, true] (cons false (runsR ((2 * b + 1) :: (r1 + 1) :: rest))) =
            rep a [true, true] (cons false (cons true (rep b [true, true]
              (cons false (cons true (rep r1 [true] (cons false (runsR rest)))))))) := by
          show rep a [true, true] (cons false (rep (2 * b + 1) [true] (cons false
            (cons true (rep r1 [true] (cons false (runsR rest))))))) = _
          rw [odd_run]
        rw [e]
        exact (Reach.of h).trans (cascB_sound ((c + a) :: hs) _ rest hp' hok)

/-- One visit from a list whose first run is even and at least 12. -/
theorem visit_sound_big (x : Nat) (tl : List Nat) (hx : x % 2 = 0) (h12 : 12 ≤ x) (hpos : ∀ r ∈ tl, 1 ≤ r) :
    (∀ l', visit (x :: tl) = some l' → ∃ n, 0 < n ∧ steps n (V (x :: tl)) = some (V l')) ∧
    (visit (x :: tl) = none → ∃ n c', steps n (V (x :: tl)) = some c' ∧ step c' = none) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = 2 * y := ⟨x / 2, by omega⟩
  have e2 : (2 * y + 2) / 2 = 1 + y := by omega
  have hv : visit (2 * y :: tl) = scan [1 + y] tl := by simp [visit, e2]
  have h : steps 5 (V (2 * y :: tl)) =
      some ⟨cons true (cons true (cons false blank)), runsR (2 * y :: tl), .E⟩ := enter (runsR (2 * y :: tl))
  have e : runsR (2 * y :: tl) = rep y [true, true] (cons false (runsR tl)) := by
    show rep (2 * y) [true] (cons false (runsR tl)) = _
    rw [pairs]
  rw [e] at h
  have ss := scan_sound tl [] 1 y (by omega) hpos (by simp) (show 7 ≤ 1 + y by omega)
  rw [hv]
  refine ⟨fun l' h' => ?_, fun h' => ?_⟩
  · obtain ⟨n, hn⟩ := ss.1 l' h'
    exact ⟨5 + n, by omega, steps_seq H175628.trans h hn⟩
  · obtain ⟨n, c', hn, hc'⟩ := ss.2 h'
    exact ⟨5 + n, c', steps_seq H175628.trans h hn, hc'⟩

/-- The first visit of an epoch: `[6, 4, 1, 1, ...]` goes to `[12, 4, ...]` (the proved sweep). -/
theorem visit_small (tl : List Nat) : visit (6 :: 4 :: 1 :: 1 :: tl) = some (12 :: 4 :: tl) := rfl

theorem visit_sound_small (tl : List Nat) :
    ∃ n, 0 < n ∧ steps n (V (6 :: 4 :: 1 :: 1 :: tl)) = some (V (12 :: 4 :: tl)) :=
  ⟨44, by omega, sweep 0 2 (runsR tl)⟩

/-! ## The domain: lists the map never leaves -/

/-- No run is empty and no run has length 2. -/
def Dr (r : Nat) : Prop := 1 ≤ r ∧ r ≠ 2

/-- The first run is even, and either at least 12 or the list starts `6, 4, 1, 1`. -/
def Hd (l : List Nat) : Prop :=
  ∃ x tl, l = x :: tl ∧ x % 2 = 0 ∧ (12 ≤ x ∨ ∃ tl', l = 6 :: 4 :: 1 :: 1 :: tl')

def D (l : List Nat) : Prop := (∀ r ∈ l, Dr r) ∧ Hd l

theorem cascC_all : ∀ (hs l : List Nat), (∀ r ∈ l, Dr r) → ∀ r ∈ cascC hs l, Dr r
  | [], l, h => by
    intro r hr
    simp only [cascC, List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
    · exact h r (List.mem_of_mem_drop hr)
  | [c], l, h => by
    intro r hr
    simp only [cascC, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨by omega, by omega⟩
    · exact h r (List.mem_of_mem_drop hr)
  | c :: t :: hs, l, h => by
    show ∀ r ∈ cascC hs (List.replicate t 1 ++ (2 * c + 4 + l.getD 1 1) :: l.drop 2), Dr r
    apply cascC_all hs
    intro r hr
    simp only [List.mem_append, List.mem_replicate, List.mem_cons] at hr
    rcases hr with ⟨_, rfl⟩ | rfl | hr
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
    · exact h r (List.mem_of_mem_drop hr)

theorem cascB_all (hs : List Nat) (w : Nat) (l : List Nat) (hw : 3 ≤ w) (h : ∀ r ∈ l, Dr r) :
    ∀ r ∈ cascB hs (w :: l), Dr r := by
  cases hs with
  | nil =>
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact ⟨by omega, by omega⟩
    · exact h r hr
  | cons t hs =>
    show ∀ r ∈ cascC hs (List.replicate t 1 ++ (w + 1) :: l), Dr r
    apply cascC_all hs
    intro r hr
    simp only [List.mem_append, List.mem_replicate, List.mem_cons] at hr
    rcases hr with ⟨_, rfl⟩ | rfl | hr
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
    · exact h r hr

theorem scan_all : ∀ (l hs l' : List Nat), (∀ r ∈ l, Dr r) → scan hs l = some l' → ∀ r ∈ l', Dr r
  | [], hs, l', _, h => by simp [scan] at h
  | r :: l, hs, l', hl, h => by
    have hl' : ∀ r ∈ l, Dr r := fun x hx => hl x (by simp [hx])
    have hr : Dr r := hl r (by simp)
    by_cases hev : r % 2 = 0
    · simp only [scan, hev, ite_true] at h
      exact scan_all l _ l' hl' h
    · cases l with
      | nil =>
        simp only [scan, hev, ite_false, Option.some.injEq] at h
        subst h
        apply cascC_all
        intro x hx
        simp only [List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with ⟨_, rfl⟩ | rfl <;> exact ⟨by omega, by omega⟩
      | cons r1 rest =>
        simp only [scan, hev, ite_false, Option.some.injEq] at h
        subst h
        have hr1 : Dr r1 := hl' r1 (by simp)
        exact cascB_all hs _ rest (by have := hr.1; have := hr1.1; omega) (fun x hx => hl' x (by simp [hx]))

theorem cascC_head : ∀ (hs l : List Nat), (∀ h ∈ hs, 2 ≤ h) → lastGe hs →
    (hs = [] → ∃ l', l = 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: l') → (∃ l', l = 1 :: 1 :: l') → Hd (cascC hs l)
  | [], l, _, _, h7, _ => by
    obtain ⟨l', rfl⟩ := h7 rfl
    exact ⟨6, _, rfl, by decide, Or.inr ⟨l', rfl⟩⟩
  | [c], l, _, hok, _, hl => by
    obtain ⟨l', rfl⟩ := hl
    have h7 : 7 ≤ c := hok
    exact ⟨2 * c + 3 + 1, l', rfl, by omega, Or.inl (by omega)⟩
  | c :: t :: hs, l, hp, hok, _, hl => by
    obtain ⟨l', rfl⟩ := hl
    have ht : 2 ≤ t := hp t (by simp)
    obtain ⟨t, rfl⟩ : ∃ t', t = t' + 2 := ⟨t - 2, by omega⟩
    show Hd (cascC hs (List.replicate (t + 2) 1 ++ (2 * c + 4 + 1) :: l'))
    apply cascC_head hs _ (fun h hh => hp h (by simp [hh])) (lastGe_tail _ _ (lastGe_tail _ _ hok))
    · intro e0; subst e0
      have h7 : 7 ≤ t + 2 := hok
      obtain ⟨k, rfl⟩ : ∃ k, t = k + 5 := ⟨t - 5, by omega⟩
      exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

theorem cascB_head (t : Nat) (hs : List Nat) (w : Nat) (l : List Nat) (hp : ∀ h ∈ t :: hs, 2 ≤ h)
    (hok : lastGe (t :: hs)) : Hd (cascB (t :: hs) (w :: l)) := by
  have ht : 2 ≤ t := hp t (by simp)
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 2 := ⟨t - 2, by omega⟩
  show Hd (cascC hs (List.replicate (t + 2) 1 ++ (w + 1) :: l))
  apply cascC_head hs _ (fun h hh => hp h (by simp [hh])) (lastGe_tail _ _ hok)
  · intro e0; subst e0
    have h7 : 7 ≤ t + 2 := hok
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 5 := ⟨t - 5, by omega⟩
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem scan_head : ∀ (l : List Nat) (h0 : Nat) (hs l' : List Nat), (∀ h ∈ h0 :: hs, 2 ≤ h) → lastGe (h0 :: hs) →
    (∀ r ∈ l, Dr r) → scan (h0 :: hs) l = some l' → Hd l'
  | [], h0, hs, l', _, _, _, h => by simp [scan] at h
  | r :: l, h0, hs, l', hp, hok, hl, h => by
    have hl' : ∀ r ∈ l, Dr r := fun x hx => hl x (by simp [hx])
    have hr : Dr r := hl r (by simp)
    by_cases hev : r % 2 = 0
    · simp only [scan, hev, ite_true] at h
      refine scan_head l (r / 2) (h0 :: hs) l' ?_ hok hl' h
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · have := hr.1; have := hr.2; omega
      · exact hp x hx
    · cases l with
      | nil =>
        simp only [scan, hev, ite_false, Option.some.injEq] at h
        subst h
        apply cascC_head (h0 :: hs) _ hp hok (by intro e0; cases e0)
        obtain ⟨k, hk⟩ : ∃ k, (r + 1) / 2 = k + 1 := ⟨(r + 1) / 2 - 1, by have := hr.1; omega⟩
        rw [hk]
        cases k with
        | zero => exact ⟨_, rfl⟩
        | succ k => exact ⟨_, rfl⟩
      | cons r1 rest =>
        simp only [scan, hev, ite_false, Option.some.injEq] at h
        subst h
        exact cascB_head h0 hs _ rest hp hok

/-- One visit, for a list of the domain: the next list is in the domain and the machine reaches it; or the map
says halt and the machine halts. -/
theorem visit_step (l : List Nat) (hD : D l) :
    (∀ l', visit l = some l' → D l' ∧ ∃ n, 0 < n ∧ steps n (V l) = some (V l')) ∧
    (visit l = none → ∃ n c', steps n (V l) = some c' ∧ step c' = none) := by
  obtain ⟨hall, x, tl, rfl, hx, hcase⟩ := hD
  have htl : ∀ r ∈ tl, Dr r := fun r hr => hall r (by simp [hr])
  rcases hcase with h12 | ⟨tl', e⟩
  · have hs := visit_sound_big x tl hx h12 (fun r hr => (htl r hr).1)
    refine ⟨fun l' h' => ⟨⟨?_, ?_⟩, hs.1 l' h'⟩, hs.2⟩
    · exact scan_all tl _ l' htl h'
    · refine scan_head tl ((x + 2) / 2) [] l' ?_ (show 7 ≤ (x + 2) / 2 by omega) htl h'
      intro h hh
      rcases List.mem_cons.1 hh with rfl | hh
      · omega
      · cases hh
  · cases e
    refine ⟨fun l' h' => ?_, fun h' => by rw [visit_small] at h'; cases h'⟩
    rw [visit_small] at h'
    cases h'
    refine ⟨⟨?_, 12, _, rfl, by decide, Or.inl (by omega)⟩, visit_sound_small tl'⟩
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact ⟨by omega, by omega⟩
    · rcases List.mem_cons.1 hr with rfl | hr
      · exact ⟨by omega, by omega⟩
      · exact hall r (by simp [hr])

/-! ## The orbit and the halting theorem -/

/-- The run list at the visit of step 423: a run of 12 and nine units. -/
def l0 : List Nat := [12, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem D_l0 : D l0 := by
  refine ⟨?_, 12, _, rfl, by decide, Or.inl (by omega)⟩
  intro r hr
  simp only [l0, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩

/-- After 423 steps from blank tape the machine is at the visit `V l0`. -/
theorem blank_to_V : steps 423 init = some (V l0) := by
  have h := blank_reaches trans (q := St.A) (n := 423) (c := ⟨[], [false, true, true, true, true, true, true, true, true, true,
    true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true,
    false, true, false, true], .B⟩) (by decide +kernel)
  have e : cons true blank = cons true (cons false blank) := by rw [cons_false_blank]
  have e' : (FCfg.toCfg (⟨[], [false, true, true, true, true, true, true, true, true, true,
    true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true,
    false, true, false, true], .B⟩ : FCfg St)) = V l0 := by
    show (⟨blank, cons false (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true
      (cons true (cons true (cons true (cons true (cons false (cons true (cons false (cons true (cons false (cons true
      (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false
      (cons true (cons false (cons true blank)))))))))))))))))))))))))))))), .B⟩ : Config) = _
    rw [e]; rfl
  rw [e'] at h
  exact h

/-- The orbit of `l0` under the visit map; `none` once the map says halt. -/
def orbit : Nat → Option (List Nat)
  | 0 => some l0
  | n + 1 => (orbit n).bind visit

/-- Every point of the orbit is in the domain and is reached, by a run of at least `n` steps. -/
theorem orbit_reached (n : Nat) (l : List Nat) (h : orbit n = some l) :
    D l ∧ ∃ m, n ≤ m ∧ steps m init = some (V l) := by
  induction n generalizing l with
  | zero =>
    simp only [orbit, Option.some.injEq] at h
    subst h
    exact ⟨D_l0, 423, by omega, blank_to_V⟩
  | succ n ih =>
    simp only [orbit] at h
    cases e : orbit n with
    | none => rw [e] at h; cases h
    | some l₁ =>
      rw [e] at h
      obtain ⟨hD, m, hm, hrun⟩ := ih l₁ e
      obtain ⟨hD', k, hk, hs⟩ := (visit_step l₁ hD).1 l h
      exact ⟨hD', m + k, by omega, steps_seq H175628.trans hrun hs⟩

/-- **The machine halts from blank tape if and only if the orbit of the visit map reaches a list with no odd run**
(the only way `visit` returns `none` on the domain). -/
theorem halts_iff : HaltsFromBlank ↔ ∃ n, orbit n = none := by
  constructor
  · intro hh
    refine Classical.byContradiction fun hne => ?_
    have hall : ∀ n, ∃ x, orbit n = some x := by
      intro n
      cases e : orbit n with
      | none => exact absurd ⟨n, e⟩ hne
      | some x => exact ⟨x, rfl⟩
    apply not_halts_of_forall H175628.trans _ hh
    apply forall_of_unbounded H175628.trans (fun m => ∃ c', steps m init = some c')
    · intro n
      obtain ⟨l, hx⟩ := hall n
      obtain ⟨_, m, hm, hrun⟩ := orbit_reached n l hx
      exact ⟨m, hm, _, hrun⟩
    · intro m hm; exact hm
  · rintro ⟨n, hn⟩
    induction n with
    | zero => cases hn
    | succ n ih =>
      cases e : orbit n with
      | none => exact ih e
      | some l =>
        simp only [orbit, e, Option.bind_some] at hn
        obtain ⟨hD, m, _, hrun⟩ := orbit_reached n l e
        obtain ⟨k, c', hs, hc⟩ := (visit_step l hD).2 hn
        exact ⟨m + k, c', steps_seq H175628.trans hrun hs, hc⟩

/-- On the domain the map says halt exactly when, after the first run, no run is odd. -/
theorem scan_none_iff : ∀ (l hs : List Nat), scan hs l = none ↔ ∀ r ∈ l, r % 2 = 0
  | [], hs => by simp [scan]
  | r :: l, hs => by
    by_cases hev : r % 2 = 0
    · simp only [scan, hev, ite_true, List.mem_cons, forall_eq_or_imp, true_and]
      exact scan_none_iff l _
    · cases l with
      | nil => simp [scan, hev]
      | cons r1 rest => simp [scan, hev]

end H175628
