import TM.RLE
import Std.Data.HashMap

/-!
# A checked accelerated simulator with symbolic jumps

This is the accelerated simulator `rsim` (`py/rsim.py` and `c/rsim_fast.cpp` in the holdout folders) rebuilt
so that every move it makes is proved.  The tape is a left rope, a left buffer, a right buffer and a right rope; a
rope is a list of runs `(w, n)` (the word `w`, nearest cell first, `n` times), nearest run first.  The head reads the
first cell of the right buffer (or of the right rope when that buffer is empty).

The counts are not numbers but linear forms `a + b·x + c·y` (`Lin`) in two variables.  A configuration whose counts
are constants is an ordinary configuration; one with variables stands for a family of them.  Each move is proved for
every value of the variables (`OK`).  So the simulator can run one *period* of a family: if a configuration `T`
reaches `shift T` (every count `a + b·x + c·y` becomes `a + b - c + b·x + c·y`, which is `T` at `(x + 1, y - 1)`),
then `T` at `(0, J)` reaches `T` at `(J, 0)`, `J` periods at once (`jump_ok`).  These are the trip-level jumps of
rsim, which there are validated by direct simulation; here each one is checked by the symbolic run of one period.

The moves:

* plain steps inside the buffers (`bsteps` of `TM/RLE.lean`);
* a **crossing**: a periodic rule (crossing `P` copies of `w` with the `D` buffer cells behind the head brings the
  head out in the same state with the same `D` cells behind it), checked once by bounded simulation and then applied
  to `⌊n / P⌋` copies at once (`cross_r`, `cross_l` of `TM/Basic.lean`); for a count with variables, `P` must divide
  their coefficients;
* unrolling one copy of a run into a buffer (the constant part of the count must be at least 1);
* rewriting a rope without changing the tape it stands for (compression of literal cells into runs, absorption of
  copies into a run, merging equal runs, dropping blank cells at the far end), each rewrite checked;
* a **jump**, as above.

Which move is tried when (learning rules, when to compress, when to look for a period and how long it is) is
unverified code: a bad choice can only make a move or a jump fail.  The result `run_ok`: when `run` reports `N`
steps, the machine makes `N` steps from blank tape without halting.
-/

namespace TM
namespace RS

/-! ## Linear counts -/

/-- The count `a + b·x + c·y`. -/
structure Lin where
  a : Nat
  b : Nat
  c : Nat
  deriving DecidableEq, Hashable, Repr, Inhabited

namespace Lin

/-- The value at `(x, y)`. -/
def ev (v : Nat × Nat) (n : Lin) : Nat := n.a + n.b * v.1 + n.c * v.2

/-- A constant. -/
def k (a : Nat) : Lin := ⟨a, 0, 0⟩

def add (m n : Lin) : Lin := ⟨m.a + n.a, m.b + n.b, m.c + n.c⟩

def mulc (n : Lin) (s : Nat) : Lin := ⟨n.a * s, n.b * s, n.c * s⟩

def isK (n : Lin) : Bool := n.b == 0 && n.c == 0

def isZero (n : Lin) : Bool := n.a == 0 && n.b == 0 && n.c == 0

/-- The count with the constant part lowered by one (when it is at least 1, its value is one less). -/
def pred (n : Lin) : Lin := ⟨n.a - 1, n.b, n.c⟩

/-- The same count one period later: `(x, y)` becomes `(x + 1, y - 1)`. -/
def shift (n : Lin) : Lin := ⟨n.a + n.b - n.c, n.b, n.c⟩

/-- The count as a constant at `v`. -/
def inst (v : Nat × Nat) (n : Lin) : Lin := k (n.ev v)

@[simp] theorem ev_k (v : Nat × Nat) (a : Nat) : (k a).ev v = a := by simp [ev, k]

@[simp] theorem ev_add (v : Nat × Nat) (m n : Lin) : (add m n).ev v = m.ev v + n.ev v := by
  simp only [ev, add]; rw [Nat.add_mul, Nat.add_mul]; omega

theorem ev_mulc (v : Nat × Nat) (n : Lin) (s : Nat) : (mulc n s).ev v = n.ev v * s := by
  simp only [ev, mulc, Nat.add_mul, Nat.mul_right_comm]

theorem ev_pred (v : Nat × Nat) (n : Lin) (h : 1 ≤ n.a) : n.ev v = (pred n).ev v + 1 := by
  simp only [ev, pred]; omega

theorem ev_of_isZero (v : Nat × Nat) {n : Lin} (h : n.isZero = true) : n.ev v = 0 := by
  obtain ⟨a, b, c⟩ := n
  simp [isZero] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  simp [ev]

theorem ev_shift (x y : Nat) (n : Lin) (h : n.c ≤ n.a + n.b) :
    (shift n).ev (x, y + 1) = n.ev (x + 1, y) := by
  simp only [ev, shift, Nat.mul_add, Nat.mul_one]
  omega

@[simp] theorem ev_inst (v w : Nat × Nat) (n : Lin) : (inst v n).ev w = n.ev v := by simp [inst]

/-- Dividing a count by `P` when `P` divides the coefficients: quotient and remainder. -/
def divP (n : Lin) (P : Nat) : Lin := ⟨n.a / P, n.b / P, n.c / P⟩

theorem ev_divP (v : Nat × Nat) (n : Lin) (P : Nat) (hb : n.b % P = 0) (hc : n.c % P = 0) :
    n.ev v = (divP n P).ev v * P + n.a % P := by
  obtain ⟨a, b, c⟩ := n
  simp only [ev, divP] at *
  have e1 : b = b / P * P := (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hb)).symm
  have e2 : c = c / P * P := (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hc)).symm
  have e3 := Nat.div_add_mod' a P
  conv => lhs; rw [e1, e2, ← e3]
  simp only [Nat.add_mul, Nat.mul_right_comm]
  omega

end Lin

/-! ## Ropes and configurations -/

abbrev Item := List Bool × Lin

/-- One side of the tape: runs, nearest first, then blank tape. -/
abbrev Side := List Item

/-- The tape a side stands for at `v`. -/
def den (v : Nat × Nat) : Side → Tape
  | [] => blank
  | (w, n) :: s => rep (n.ev v) w (den v s)

@[simp] theorem den_nil (v : Nat × Nat) : den v [] = blank := rfl
@[simp] theorem den_cons (v : Nat × Nat) (w : List Bool) (n : Lin) (s : Side) :
    den v ((w, n) :: s) = rep (n.ev v) w (den v s) := rfl

/-- The word `w` written `P` times. -/
def flat (P : Nat) (w : List Bool) : List Bool := (List.replicate P w).flatten

theorem app_flat (P : Nat) (w : List Bool) (s : Tape) : app (flat P w) s = rep P w s := by
  induction P with
  | zero => rfl
  | succ P ih =>
    simp only [flat, List.replicate_succ, List.flatten_cons] at *
    rw [← app_app, ih]; rfl

theorem rep_mul_flat (k P : Nat) (w : List Bool) (s : Tape) : rep (k * P) w s = rep k (flat P w) s := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.succ_mul, Nat.add_comm, rep_add, ih, rep_succ, app_flat]

/-- A configuration: left rope, left buffer (nearest first), right buffer (head on its first cell), right rope. -/
structure SCfg (Q : Type) where
  L : Side
  ll : List Bool
  rr : List Bool
  R : Side
  q : Q
  deriving DecidableEq

variable {Q : Type}

def SCfg.den (v : Nat × Nat) (c : SCfg Q) : Cfg Q := ⟨app c.ll (RS.den v c.L), app c.rr (RS.den v c.R), c.q⟩

section
variable (δ : Q → Bool → Option (Bool × Dir × Q))

/-- `c` reaches `c'` in `s` steps, at every value of the variables. -/
def OK (c c' : SCfg Q) (s : Lin) : Prop := ∀ v, steps δ (s.ev v) (c.den v) = some (c'.den v)

theorem OK.refl (c : SCfg Q) : OK δ c c (Lin.k 0) := fun v => by simp

theorem OK.trans {c₁ c₂ c₃ : SCfg Q} {s t : Lin} (h₁ : OK δ c₁ c₂ s) (h₂ : OK δ c₂ c₃ t) :
    OK δ c₁ c₃ (Lin.add s t) := fun v => by
  rw [Lin.ev_add]; exact steps_seq δ (h₁ v) (h₂ v)

theorem OK.of_eq {c c' : SCfg Q} (h : ∀ v, c.den v = c'.den v) : OK δ c c' (Lin.k 0) := fun v => by
  simp [h v]

end

/-! ## Rewriting a side without changing its tape -/

/-- The cells of a side made of constant runs (`none` for a count with variables). -/
def expand : Side → Option (List Bool)
  | [] => some []
  | (w, n) :: s =>
    if n.isK then (expand s).map (fun x => flat n.a w ++ x) else none

theorem den_append_of_expand (v : Nat × Nat) : ∀ (p : Side) (x : List Bool) (t : Side),
    expand p = some x → den v (p ++ t) = app x (den v t)
  | [], x, t, h => by simp [expand] at h; subst h; rfl
  | (w, n) :: p, x, t, h => by
    simp only [expand] at h
    split at h
    · rename_i hk
      cases e : expand p with
      | none => rw [e] at h; cases h
      | some y =>
        rw [e] at h
        simp at h
        subst h
        obtain ⟨a, b, c⟩ := n
        simp [Lin.isK] at hk
        obtain ⟨rfl, rfl⟩ := hk
        simp only [List.cons_append, den_cons, Lin.ev, Nat.zero_mul, Nat.add_zero]
        rw [den_append_of_expand v p y t e, ← app_app, app_flat]
    · cases h

/-- A literal item. -/
def lit (x : List Bool) : Item := (x, Lin.k 1)

theorem den_lit (v : Nat × Nat) (x : List Bool) (s : Side) : den v (lit x :: s) = app x (den v s) := by
  simp [lit, den_cons, Lin.ev_k]

theorem blank_eq_app_false (n : Nat) : blank = app (List.replicate n false) blank := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, app_cons, ← ih, cons_false_blank]

/-- All cells blank. -/
def allFalse (x : List Bool) : Bool := x.all (· == false)

theorem app_allFalse_blank {x : List Bool} (h : allFalse x = true) : app x blank = blank := by
  induction x with
  | nil => rfl
  | cons a x ih =>
    simp [allFalse] at h
    obtain ⟨rfl, h2⟩ := h
    rw [app_cons, ih (by simp [allFalse]; exact h2), cons_false_blank]

theorem rep_allFalse_blank {x : List Bool} (h : allFalse x = true) (n : Nat) : rep n x blank = blank := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep_succ, ih, app_allFalse_blank h]

/-! ### Compression (unverified; its output is checked) -/

/-- The least rotation of a word (as a rotation offset). -/
def minRot (w : List Bool) : Nat := Id.run do
  let n := w.length
  let mut best := w
  let mut r := 0
  for i in [1:n] do
    let c := w.drop i ++ w.take i
    if decide (c < best) then
      best := c; r := i
  return r

/-- The shortest root of a word (`w = root^k`). -/
def root (w : List Bool) : List Bool := Id.run do
  let n := w.length
  for p in [1:n / 2 + 1] do
    if n % p == 0 && flat (n / p) (w.take p) == w then return w.take p
  return w

/-- Greedy compression of literal cells into runs of short words (the `compress1` of rsim): at each position the
repeat of period at most `maxp` with at least 3 copies covering the most cells (at least 6), its word turned to its
least rotation. -/
partial def compress (s : Array Bool) (maxp : Nat := 32) : Side := Id.run do
  let n := s.size
  let mut out : Array Item := #[]
  let mut i := 0
  let mut loose := 0
  let word := fun (i p : Nat) => (s.extract i (i + p)).toList
  let copies := fun (i p : Nat) => Id.run do
    let mut k := i + p
    while k < n && s[k]! == s[k - p]! do
      k := k + 1
    return (k - i) / p
  while i < n do
    let mut best := 0
    let mut bp := 0
    for p in [1:maxp + 1] do
      if i + 3 * p ≤ n && s[i + p]! == s[i]! && s[i + 2 * p]! == s[i]! && s[i + p + 1]! == s[i + 1]! then
        let r := copies i p
        if r ≥ 3 && r * p ≥ 6 && r * p > best then
          best := r * p; bp := p
    if best > 0 then
      let o := minRot (word i bp)
      let i' := i + o
      let r := if i' + bp ≤ n then copies i' bp else 0
      if r ≥ 2 then
        if loose < i' then out := out.push (lit (s.extract loose i').toList)
        out := out.push (word i' bp, Lin.k r)
        i := i' + r * bp
        loose := i
      else
        i := i + 1
    else
      i := i + 1
  if loose < n then out := out.push (lit (s.extract loose n).toList)
  return out.toList

section CF
-- The compression used (unverified: `compress`, or a table of its earlier results).
variable (cf : List Bool → Side)

/-- Compressed literal cells, checked: the runs spell `x`. -/
def compressChecked (x : List Bool) : Side :=
  let p := cf x
  if expand p = some x then p else [lit x]

theorem compressChecked_spec (x : List Bool) : expand (compressChecked cf x) = some x := by
  unfold compressChecked
  simp only
  split
  · assumption
  · simp [expand, lit, Lin.isK, Lin.k, flat]

/-! ### Canonical form of a side

A side is cut into *big* runs (a count with variables, a constant of at least `BIG`, or long) and the literal cells
between them.  Copies of a big run's word next to it are absorbed into it, big runs with the same word are merged,
the cells between are compressed, and blank cells at the far end are dropped.  This is the signature of rsim's
samples: two configurations with the same signature differ only in the counts of their big runs. -/

def BIG : Nat := 8
def LONG : Nat := 4096

def isBig (it : Item) : Bool := !it.2.isK || decide (BIG ≤ it.2.a) || decide (LONG < it.1.length * it.2.a)

/-- Split off the small runs in front (at most `lim` of them). -/
def spanSmall : Nat → Side → Side × Side
  | 0, s => ([], s)
  | _, [] => ([], [])
  | lim + 1, it :: s => if isBig it then ([], it :: s) else
      let p := spanSmall lim s
      (it :: p.1, p.2)

theorem spanSmall_eq : ∀ (lim : Nat) (s : Side), (spanSmall lim s).1 ++ (spanSmall lim s).2 = s
  | 0, s => rfl
  | _ + 1, [] => rfl
  | lim + 1, it :: s => by
    unfold spanSmall
    split
    · rfl
    · simp [spanSmall_eq lim s]

/-- `x = y ++ w^j` for the largest `j`: returns `(y, j)`. -/
def stripFar (x w : List Bool) : List Bool × Nat := Id.run do
  if w.isEmpty then return (x, 0)
  let mut y := x
  let mut j := 0
  let rw := w.reverse
  let mut ry := x.reverse
  while rw.isPrefixOf ry do
    ry := ry.drop w.length
    j := j + 1
  y := ry.reverse
  return (y, j)

/-- `x = w^j ++ y` for the largest `j`: returns `(j, y)`. -/
def stripNear (x w : List Bool) : Nat × List Bool := Id.run do
  if w.isEmpty then return (0, x)
  let mut y := x
  let mut j := 0
  while w.isPrefixOf y do
    y := y.drop w.length
    j := j + 1
  return (j, y)

/-- Drop blank cells at the end of a word. -/
def dropFalseEnd (x : List Bool) : List Bool := (x.reverse.dropWhile (· == false)).reverse

theorem app_append_false_blank (y : List Bool) (k : Nat) : app (y ++ List.replicate k false) blank = app y blank := by
  rw [← app_app, ← blank_eq_app_false]

/-- The cells `x` (nearest first) put in front of `t`, where `t` starts with a big run: copies of its word at the
far end of `x` join it, and the rest is compressed. When `t` is empty (blank tape follows), blank cells at the end of
`x` are dropped. -/
def placeCells (x : List Bool) (t : Side) : Side :=
  match t with
  | [] =>
    let y := dropFalseEnd x
    if y ++ List.replicate (x.length - y.length) false = x then compressChecked cf y else compressChecked cf x
  | (w, n) :: t' =>
    let p := stripFar x w
    if p.1 ++ flat p.2 w = x then compressChecked cf p.1 ++ (w, Lin.add n (Lin.k p.2)) :: t'
    else compressChecked cf x ++ t

theorem den_placeCells cf (v : Nat × Nat) (x : List Bool) (t : Side) : den v (placeCells cf x t) = app x (den v t) := by
  unfold placeCells
  match t with
  | [] =>
    simp only
    split
    · rename_i h
      rw [← List.append_nil (compressChecked cf _), den_append_of_expand v _ _ _ (compressChecked_spec cf _)]
      conv => rhs; rw [← h]
      rw [den_nil, app_append_false_blank]
    · rw [← List.append_nil (compressChecked cf _), den_append_of_expand v _ _ _ (compressChecked_spec cf _)]
  | (w, n) :: t' =>
    simp only
    split
    · rename_i h
      rw [den_append_of_expand v _ _ _ (compressChecked_spec cf _)]
      conv => rhs; rw [← h]
      rw [← app_app, app_flat, den_cons, den_cons, Lin.ev_add, Lin.ev_k, Nat.add_comm, rep_add]
    · rw [den_append_of_expand v _ _ _ (compressChecked_spec cf _)]

/-- Copies of the word `w` of a big run with count `n` at the near end of the cells `x` behind it join it. -/
def joinNear (w : List Bool) (n : Lin) (x : List Bool) : Lin × List Bool :=
  let p := stripNear x w
  if flat p.1 w ++ p.2 = x then (Lin.add n (Lin.k p.1), p.2) else (n, x)

theorem joinNear_spec (v : Nat × Nat) (w : List Bool) (n : Lin) (x : List Bool) (S : Tape) :
    rep ((joinNear w n x).1.ev v) w (app (joinNear w n x).2 S) = rep (n.ev v) w (app x S) := by
  unfold joinNear
  simp only
  split
  · rename_i h
    conv => rhs; rw [← h]
    rw [← app_app, app_flat, ← rep_add, Lin.ev_add, Lin.ev_k]
  · rfl

/-- Merge a run with an equal-word run behind it. -/
def mergeRuns : Side → Side
  | (w, n) :: (w', n') :: t => if w = w' then (w, Lin.add n n') :: t else (w, n) :: (w', n') :: t
  | s => s

theorem den_mergeRuns (v : Nat × Nat) (s : Side) : den v (mergeRuns s) = den v s := by
  unfold mergeRuns
  split
  · split
    · rename_i h; subst h; simp [rep_add]
    · rfl
  · rfl

theorem den_append_congr (v : Nat × Nat) : ∀ (a : Side) {b b' : Side}, den v b = den v b' →
    den v (a ++ b) = den v (a ++ b')
  | [], _, _, h => h
  | (w, n) :: a, _, _, h => by simp [den_append_congr v a h]

/-- The canonical form of the near part of a side: the small runs in front (up to `lim`) and the cells they spell
are re-compressed and joined to the big run behind them. -/
def canonNear (lim : Nat) (s : Side) : Side :=
  let p := spanSmall lim s
  match expand p.1 with
  | none => s
  | some x => if x.isEmpty then p.2 else placeCells cf x p.2

theorem den_canonNear (v : Nat × Nat) (lim : Nat) (s : Side) : den v (canonNear cf lim s) = den v s := by
  unfold canonNear
  simp only
  have hs := spanSmall_eq lim s
  split
  · rfl
  · rename_i x hx
    have e := den_append_of_expand v _ x (spanSmall lim s).2 hx
    rw [hs] at e
    split
    · rename_i h
      simp at h; subst h; rw [e]; rfl
    · rw [e, den_placeCells cf]

def CLIM : Nat := 1000000

/-- The canonical form of a whole side. -/
def canonSide : Nat → Side → Side
  | 0, s => s
  | fuel + 1, s =>
    let s1 := canonNear cf CLIM s
    let p := spanSmall CLIM s1
    match p.2 with
    | [] => s1
    | (w, n) :: t =>
      let t1 := canonSide fuel t
      let q := spanSmall CLIM t1
      match expand q.1 with
      | none => p.1 ++ mergeRuns ((w, n) :: t1)
      | some x =>
        let j := joinNear w n x
        if j.2.isEmpty then p.1 ++ mergeRuns ((w, j.1) :: q.2)
        else p.1 ++ ((w, j.1) :: (compressChecked cf j.2 ++ q.2))

theorem den_canonSide (v : Nat × Nat) : ∀ (fuel : Nat) (s : Side), den v (canonSide cf fuel s) = den v s
  | 0, s => rfl
  | fuel + 1, s => by
    unfold canonSide
    have h1 := den_canonNear cf v CLIM s
    generalize canonNear cf CLIM s = s1 at h1 ⊢
    have hs := spanSmall_eq CLIM s1
    rcases hp : spanSmall CLIM s1 with ⟨p1, p2⟩
    simp only [hp] at hs ⊢
    match p2, hs with
    | [], hs => exact h1
    | (w, n) :: t, hs =>
      simp only
      rw [← h1, ← hs]
      have ih := den_canonSide v fuel t
      generalize canonSide cf fuel t = t1 at ih ⊢
      have hq := spanSmall_eq CLIM t1
      rcases hq' : spanSmall CLIM t1 with ⟨q1, q2⟩
      simp only [hq'] at hq ⊢
      cases hx : expand q1 with
      | none =>
        simp only
        apply den_append_congr
        rw [den_mergeRuns, den_cons, den_cons, ih]
      | some x =>
        simp only
        have e := den_append_of_expand v q1 x q2 hx
        rw [hq, ih] at e
        split
        · rename_i hj
          apply den_append_congr
          rw [den_mergeRuns, den_cons, den_cons, e, ← joinNear_spec v w n x]
          simp at hj; rw [hj]; rfl
        · apply den_append_congr
          rw [den_cons, den_append_of_expand v _ _ _ (compressChecked_spec cf _), den_cons, e, joinNear_spec]

end CF

/-- `compress`, with a table of earlier results. -/
def memoCF (m : Std.HashMap (List Bool) Side) (x : List Bool) : Side :=
  match m.get? x with
  | some p => p
  | none => compress x.toArray

/-- Record the small-run segments of a side (at most `lim` items) as compressions of the cells they spell. -/
def recordSegs (m : Std.HashMap (List Bool) Side) (lim : Nat) (s : Side) : Std.HashMap (List Bool) Side :=
  let rec go : Nat → Side → Side → Std.HashMap (List Bool) Side → Std.HashMap (List Bool) Side
    | 0, _, _, m => m
    | _ + 1, [], acc, m => flush acc m
    | f + 1, it :: s, acc, m => if isBig it then go f s [] (flush acc m) else go f s (it :: acc) m
  go lim s [] (if m.size > 200000 then {} else m)
where
  flush (acc : Side) (m : Std.HashMap (List Bool) Side) : Std.HashMap (List Bool) Side :=
    if acc.isEmpty then m else
    let seg := acc.reverse
    match expand seg with
    | some x => if x.length ≤ 4096 then m.insert x seg else m
    | none => m

/-! ## Moves -/

section Moves
variable [DecidableEq Q] (δ : Q → Bool → Option (Bool × Dir × Q))

/-- A move from `c`: the configuration reached and the steps, proved. -/
abbrev Mv (c : SCfg Q) := {p : SCfg Q × Lin // OK δ c p.1 p.2}

/-- No move. -/
def Mv.stay (c : SCfg Q) : Mv δ c := ⟨(c, Lin.k 0), OK.refl δ c⟩

def Mv.trans {c : SCfg Q} (m : Mv δ c) (m' : Mv δ m.1.1) : Mv δ c :=
  ⟨(m'.1.1, Lin.add m.1.2 m'.1.2), OK.trans δ m.2 m'.2⟩

/-- A rewrite that keeps the tape. -/
def Mv.same {c : SCfg Q} (c' : SCfg Q) (h : ∀ v, c.den v = c'.den v) : Mv δ c := ⟨(c', Lin.k 0), OK.of_eq δ h⟩

/-! ### Plain steps in the buffers -/

def runBuf : Nat → List Bool × List Bool × Q → Nat → (List Bool × List Bool × Q) × Nat
  | 0, c, n => (c, n)
  | f + 1, c, n =>
    match bstep δ c with
    | none => (c, n)
    | some c' => runBuf f c' (n + 1)

omit [DecidableEq Q] in
theorem runBuf_spec : ∀ (f : Nat) (c : List Bool × List Bool × Q) (n : Nat),
    n ≤ (runBuf δ f c n).2 ∧ bsteps δ ((runBuf δ f c n).2 - n) c = some (runBuf δ f c n).1
  | 0, c, n => by simp [runBuf, bsteps]
  | f + 1, c, n => by
    unfold runBuf
    cases e : bstep δ c with
    | none => simp [bsteps]
    | some c' =>
      simp only
      obtain ⟨h1, h2⟩ := runBuf_spec f c' (n + 1)
      refine ⟨by omega, ?_⟩
      have e2 : (runBuf δ f c' (n + 1)).2 - n = ((runBuf δ f c' (n + 1)).2 - (n + 1)) + 1 := by omega
      rw [e2]
      simp only [bsteps, e]
      exact h2

/-- The same loop without the intermediate tuples (the one that runs). -/
def runBuf2 : Nat → List Bool → List Bool → Q → Nat → List Bool × List Bool × Q × Nat
  | 0, l, r, q, n => (l, r, q, n)
  | _ + 1, l, [], q, n => (l, [], q, n)
  | f + 1, l, a :: r, q, n =>
    match δ q a with
    | none => (l, a :: r, q, n)
    | some (w, .R, s) => runBuf2 f (w :: l) r s (n + 1)
    | some (w, .L, s) =>
      match l with
      | [] => ([], a :: r, q, n)
      | b :: l' => runBuf2 f l' (b :: w :: r) s (n + 1)

omit [DecidableEq Q] in
theorem runBuf2_eq : ∀ (f : Nat) (l r : List Bool) (q : Q) (n : Nat),
    runBuf2 δ f l r q n = ((runBuf δ f (l, r, q) n).1.1, (runBuf δ f (l, r, q) n).1.2.1,
      (runBuf δ f (l, r, q) n).1.2.2, (runBuf δ f (l, r, q) n).2)
  | 0, l, r, q, n => rfl
  | f + 1, l, [], q, n => by simp [runBuf2, runBuf, bstep]
  | f + 1, l, a :: r, q, n => by
    unfold runBuf2 runBuf
    simp only [bstep]
    cases e : δ q a with
    | none => rfl
    | some t =>
      obtain ⟨w, d, s⟩ := t
      cases d with
      | R => simp only; exact runBuf2_eq f _ _ _ _
      | L =>
        cases l with
        | nil => rfl
        | cons b l' => simp only; exact runBuf2_eq f _ _ _ _

/-- Plain steps until the head leaves the buffers (or `f` steps). -/
def mPlain (f : Nat) (c : SCfg Q) : Mv δ c :=
  let r := runBuf2 δ f c.ll c.rr c.q 0
  ⟨(⟨c.L, r.1, r.2.1, c.R, r.2.2.1⟩, Lin.k r.2.2.2), fun v => by
    have h := (runBuf_spec δ f (c.ll, c.rr, c.q) 0).2
    simp only [Nat.sub_zero] at h
    have := bsteps_spec δ _ h (RS.den v c.L) (RS.den v c.R)
    simp only [r, runBuf2_eq]
    simpa [SCfg.den] using this⟩

/-! ### Blank cells, unrolling, dropping empty runs -/

theorem den_pred_unroll (v : Nat × Nat) (w : List Bool) (n : Lin) (h : 1 ≤ n.a) (s : Side) (x : List Bool) :
    app x (RS.den v ((w, n) :: s)) = app (x ++ w) (RS.den v ((w, n.pred) :: s)) := by
  simp only [den_cons]
  rw [Lin.ev_pred v n h, rep_succ, app_app]

/-- Fetch cells from the right rope to the far end of the right buffer. -/
def mFetchR (c : SCfg Q) : Option (Mv δ c) :=
  match hR : c.R with
  | [] => some (Mv.same δ ⟨c.L, c.ll, c.rr ++ List.replicate 64 false, [], c.q⟩ (fun v => by
      simp only [SCfg.den, hR, den_nil]
      rw [← app_app, ← blank_eq_app_false]))
  | (w, n) :: R' =>
    if hz : n.isZero then some (Mv.same δ ⟨c.L, c.ll, c.rr, R', c.q⟩ (fun v => by
      simp [SCfg.den, hR, Lin.ev_of_isZero v hz]))
    else if h1 : 1 ≤ n.a then some (Mv.same δ ⟨c.L, c.ll, c.rr ++ w, (w, n.pred) :: R', c.q⟩ (fun v => by
      simp only [SCfg.den, hR]
      rw [den_pred_unroll v w n h1 R' c.rr]))
    else none

/-- Fetch cells from the left rope to the far end of the left buffer. -/
def mFetchL (c : SCfg Q) : Option (Mv δ c) :=
  match hL : c.L with
  | [] => some (Mv.same δ ⟨[], c.ll ++ List.replicate 64 false, c.rr, c.R, c.q⟩ (fun v => by
      simp only [SCfg.den, hL, den_nil]
      rw [← app_app, ← blank_eq_app_false]))
  | (w, n) :: L' =>
    if hz : n.isZero then some (Mv.same δ ⟨L', c.ll, c.rr, c.R, c.q⟩ (fun v => by
      simp [SCfg.den, hL, Lin.ev_of_isZero v hz]))
    else if h1 : 1 ≤ n.a then some (Mv.same δ ⟨(w, n.pred) :: L', c.ll ++ w, c.rr, c.R, c.q⟩ (fun v => by
      simp only [SCfg.den, hL]
      rw [den_pred_unroll v w n h1 L' c.ll]))
    else none

theorem Lin.ev_of_isK (v : Nat × Nat) {n : Lin} (h : n.isK = true) : n.ev v = n.a := by
  obtain ⟨a, b, c⟩ := n
  simp [Lin.isK] at h
  obtain ⟨rfl, rfl⟩ := h
  simp [Lin.ev]

/-- Fetch a whole short constant run from the right rope (else one copy, as `mFetchR`). -/
def mFetchAllR (c : SCfg Q) : Option (Mv δ c) :=
  match hR : c.R with
  | (w, n) :: R' =>
    if hk : n.isK ∧ n.a * w.length ≤ 256 then some (Mv.same δ ⟨c.L, c.ll, c.rr ++ flat n.a w, R', c.q⟩ (fun v => by
      simp only [SCfg.den, hR, den_cons, Lin.ev_of_isK v hk.1]
      rw [← app_app, app_flat]))
    else mFetchR δ c
  | [] => mFetchR δ c

def mFetchAllL (c : SCfg Q) : Option (Mv δ c) :=
  match hL : c.L with
  | (w, n) :: L' =>
    if hk : n.isK ∧ n.a * w.length ≤ 256 then some (Mv.same δ ⟨L', c.ll ++ flat n.a w, c.rr, c.R, c.q⟩ (fun v => by
      simp only [SCfg.den, hL, den_cons, Lin.ev_of_isK v hk.1]
      rw [← app_app, app_flat]))
    else mFetchL δ c
  | [] => mFetchL δ c

/-! ### Crossing rules -/

/-- A rule for crossing to the right: in state `q`, with the cells `u` behind the head (nearest first), `P` copies
of `w` are crossed in `st` steps, leaving `u` behind the head and the cells `v` behind `u`. -/
structure RuleR (Q : Type) where
  q : Q
  u : List Bool
  w : List Bool
  P : Nat
  v : List Bool
  st : Nat

def RuleR.Valid (r : RuleR Q) : Prop := bsteps δ r.st (r.u, flat r.P r.w, r.q) = some (r.u ++ r.v, [], r.q) ∧ 0 < r.P

/-- The same to the left: `u` is the cells from the head on (nearest first), `w` is on the left. -/
structure RuleL (Q : Type) where
  q : Q
  u : List Bool
  w : List Bool
  P : Nat
  v : List Bool
  st : Nat

def RuleL.Valid (r : RuleL Q) : Prop := bsteps δ r.st (flat r.P r.w, r.u, r.q) = some ([], r.u ++ r.v, r.q) ∧ 0 < r.P

abbrev VRuleR := {r : RuleR Q // r.Valid δ}
abbrev VRuleL := {r : RuleL Q // r.Valid δ}

instance (r : RuleR Q) : Decidable (r.Valid δ) := by unfold RuleR.Valid; infer_instance
instance (r : RuleL Q) : Decidable (r.Valid δ) := by unfold RuleL.Valid; infer_instance

theorem cross_count (v : Nat × Nat) (n : Lin) (P : Nat) (hb : n.b % P = 0) (hc : n.c % P = 0) (w : List Bool)
    (s : Tape) : rep (n.ev v) w s = rep ((n.divP P).ev v) (flat P w) (rep (n.a % P) w s) := by
  rw [Lin.ev_divP v n P hb hc, rep_add, rep_mul_flat]

/-- Why a crossing did not apply. -/
inductive CrossFail
  | noMatch
  | divides (P : Nat)

/-- Apply a right rule: the head is at the start of the right rope (`rr = []`). -/
def mCrossR (r : VRuleR δ) (c : SCfg Q) : Except CrossFail (Mv δ c) :=
  match hR : c.R with
  | [] => .error .noMatch
  | (w, n) :: R' =>
    if hc : c.rr = [] ∧ r.1.q = c.q ∧ r.1.w = w ∧ c.ll.take r.1.u.length = r.1.u then
      if hd : n.b % r.1.P = 0 ∧ n.c % r.1.P = 0 then
        let k := n.divP r.1.P
        .ok ⟨(⟨(r.1.v, k) :: lit (c.ll.drop r.1.u.length) :: c.L, r.1.u, [], (w, Lin.k (n.a % r.1.P)) :: R', c.q⟩,
          k.mulc r.1.st), fun v => by
          obtain ⟨hrr, hq, hw, hu⟩ := hc
          obtain ⟨hv, _⟩ := r.2
          have one : ∀ L R : Tape, steps δ r.1.st ⟨app r.1.u L, app (flat r.1.P r.1.w) R, r.1.q⟩ =
              some ⟨app r.1.u (app r.1.v L), R, r.1.q⟩ := by
            intro L R
            have := bsteps_spec δ r.1.st hv L R
            rwa [app_app]
          have hx := cross_r δ one (k.ev v) (app (c.ll.drop r.1.u.length) (RS.den v c.L))
            (rep (n.a % r.1.P) w (RS.den v R'))
          have ell : c.ll = r.1.u ++ c.ll.drop r.1.u.length := by
            conv => lhs; rw [← List.take_append_drop r.1.u.length c.ll]
            rw [hu]
          simp only [SCfg.den, hR, hrr, den_cons, app_nil, Lin.ev_mulc, den_lit, Lin.ev_k]
          rw [ell, ← app_app, cross_count v n r.1.P hd.1 hd.2, ← hq]
          subst hw
          rw [List.drop_left' rfl] at *
          exact hx⟩
      else .error (.divides r.1.P)
    else .error .noMatch

/-- Apply a left rule: the head is at the start of the right buffer, with the left buffer empty. -/
def mCrossL (r : VRuleL δ) (c : SCfg Q) : Except CrossFail (Mv δ c) :=
  match hL : c.L with
  | [] => .error .noMatch
  | (w, n) :: L' =>
    if hc : c.ll = [] ∧ r.1.q = c.q ∧ r.1.w = w ∧ c.rr.take r.1.u.length = r.1.u then
      if hd : n.b % r.1.P = 0 ∧ n.c % r.1.P = 0 then
        let k := n.divP r.1.P
        .ok ⟨(⟨(w, Lin.k (n.a % r.1.P)) :: L', [], r.1.u, (r.1.v, k) :: lit (c.rr.drop r.1.u.length) :: c.R, c.q⟩,
          k.mulc r.1.st), fun v => by
          obtain ⟨hll, hq, hw, hu⟩ := hc
          obtain ⟨hv, _⟩ := r.2
          have one : ∀ L R : Tape, steps δ r.1.st ⟨app (flat r.1.P r.1.w) L, app r.1.u R, r.1.q⟩ =
              some ⟨L, app r.1.u (app r.1.v R), r.1.q⟩ := by
            intro L R
            have := bsteps_spec δ r.1.st hv L R
            rwa [app_app]
          have hx := cross_l δ one (k.ev v) (rep (n.a % r.1.P) w (RS.den v L'))
            (app (c.rr.drop r.1.u.length) (RS.den v c.R))
          have err : c.rr = r.1.u ++ c.rr.drop r.1.u.length := by
            conv => lhs; rw [← List.take_append_drop r.1.u.length c.rr]
            rw [hu]
          simp only [SCfg.den, hL, hll, den_cons, app_nil, Lin.ev_mulc, den_lit, Lin.ev_k]
          rw [err, ← app_app, cross_count v n r.1.P hd.1 hd.2, ← hq]
          subst hw
          rw [List.drop_left' rfl] at *
          exact hx⟩
      else .error (.divides r.1.P)
    else .error .noMatch

/-! ### Moving cells between buffers and ropes -/

/-- Move the left buffer beyond its first `K` cells to the left rope. -/
def mFlushL (cf : List Bool → Side) (K lim : Nat) (c : SCfg Q) : Mv δ c :=
  Mv.same δ ⟨canonNear cf lim (lit (c.ll.drop K) :: c.L), c.ll.take K, c.rr, c.R, c.q⟩ (fun v => by
    simp only [SCfg.den, den_canonNear cf, den_lit, app_app, List.take_append_drop])

def mFlushR (cf : List Bool → Side) (K lim : Nat) (c : SCfg Q) : Mv δ c :=
  Mv.same δ ⟨c.L, c.ll, c.rr.take K, canonNear cf lim (lit (c.rr.drop K) :: c.R), c.q⟩ (fun v => by
    simp only [SCfg.den, den_canonNear cf, den_lit, app_app, List.take_append_drop])

/-- A run with its word made primitive. -/
def primItem (w : List Bool) (n : Lin) : Item :=
  let r := root w
  let k := w.length / r.length
  if r.length < w.length ∧ flat k r = w then (r, n.mulc k) else (w, n)

theorem primItem_spec (v : Nat × Nat) (w : List Bool) (n : Lin) (S : Tape) :
    rep ((primItem w n).2.ev v) (primItem w n).1 S = rep (n.ev v) w S := by
  unfold primItem
  simp only
  split
  · rename_i hc
    simp only [Lin.ev_mulc]
    rw [rep_mul_flat, hc.2]
  · rfl

/-- A run with its word turned to its least rotation, the cells moved to its sides. -/
def rotItem (w : List Bool) (n : Lin) : Side :=
  let o := minRot w
  if o = 0 ∨ n.a = 0 then [(w, n)] else [lit (w.take o), (w.drop o ++ w.take o, n.pred), lit (w.drop o)]

theorem den_rotItem (v : Nat × Nat) (w : List Bool) (n : Lin) (S : Side) :
    den v (rotItem w n ++ S) = den v ((w, n) :: S) := by
  unfold rotItem
  simp only
  split
  · rfl
  · rename_i hc
    have ha : 1 ≤ n.a := by omega
    simp only [List.cons_append, List.nil_append, den_lit, den_cons]
    rw [Lin.ev_pred v n ha, rep_succ]
    generalize minRot w = o
    have hw := List.take_append_drop o w
    conv => rhs; rw [← hw]
    rw [← app_app]
    congr 1
    rw [rep_rotate _ (w.drop o) (w.take o ++ w.drop o) (w.drop o ++ w.take o) (by simp)]

def normItem (it : Item) : Side :=
  if it.1.length ≤ 64 then rotItem (primItem it.1 it.2).1 (primItem it.1 it.2).2 else [it]

theorem den_normItem (v : Nat × Nat) (it : Item) (S : Side) : den v (normItem it ++ S) = den v (it :: S) := by
  unfold normItem
  split
  · rw [den_rotItem, den_cons, den_cons, primItem_spec]
  · rfl

/-- `normItem` on the big runs of a side. -/
def normBig : Side → Side
  | [] => []
  | it :: s => if isBig it then normItem it ++ normBig s else it :: normBig s

theorem den_normBig (v : Nat × Nat) : ∀ (s : Side), den v (normBig s) = den v s
  | [] => rfl
  | (w, n) :: s => by
    unfold normBig
    split
    · rw [den_normItem, den_cons, den_cons, den_normBig v s]
    · rw [den_cons, den_cons, den_normBig v s]

/-- Both buffers into the ropes, and both ropes in canonical form. -/
def canonCfg (cf : List Bool → Side) (c : SCfg Q) : SCfg Q :=
  ⟨canonSide cf (3 * c.L.length + 2) (normBig (lit c.ll :: c.L)), [], [],
    canonSide cf (3 * c.R.length + 2) (normBig (lit c.rr :: c.R)), c.q⟩

omit [DecidableEq Q] in
theorem den_canonCfg (cf : List Bool → Side) (v : Nat × Nat) (c : SCfg Q) : (canonCfg cf c).den v = c.den v := by
  simp [canonCfg, SCfg.den, den_canonSide cf, den_normBig, den_lit]

def mCanon (cf : List Bool → Side) (c : SCfg Q) : Mv δ c := Mv.same δ (canonCfg cf c) (fun v => (den_canonCfg cf v c).symm)

/-- Fetch cells until the left buffer has at least `m` (or the rope cannot give more). -/
def mEnsureL (m : Nat) : Nat → (c : SCfg Q) → Mv δ c
  | 0, c => Mv.stay δ c
  | f + 1, c =>
    if m ≤ c.ll.length then Mv.stay δ c else
    match mFetchL δ c with
    | none => Mv.stay δ c
    | some mv => mv.trans δ (mEnsureL m f mv.1.1)

def mEnsureR (m : Nat) : Nat → (c : SCfg Q) → Mv δ c
  | 0, c => Mv.stay δ c
  | f + 1, c =>
    if m ≤ c.rr.length then Mv.stay δ c else
    match mFetchR δ c with
    | none => Mv.stay δ c
    | some mv => mv.trans δ (mEnsureR m f mv.1.1)

/-! ### Learning rules (unverified search; the rules found are checked) -/

def KREP : Nat := 10
def SCRATCH : Nat := 400000

/-- Search a right rule: run `trail | w^K` from state `q` and look for the first moment the head is in state `q` at
the start of a later copy with the same cells behind it, as far back as it looked (each candidate is checked). -/
def learnR (q : Q) (trail w : List Bool) : Option (RuleR Q) := Id.run do
  let lw := w.length
  if lw == 0 then return none
  let tot := KREP * lw
  let mut cfg : List Bool × List Bool × Q := (trail, flat KREP w, q)
  let mut rlen := tot
  let mut t := 0
  let mut back : Nat := 0      -- how far left of the start the head has been
  let mut cur : Int := 0       -- head position relative to the start (right positive)
  while t < SCRATCH do
    match cfg.2.1 with
    | [] => return none
    | a :: _ =>
      let right := match δ cfg.2.2 a with
        | some (_, .R, _) => true
        | _ => false
      match bstep δ cfg with
      | none => return none
      | some c' =>
        cfg := c'
        t := t + 1
        if right then
          rlen := rlen - 1; cur := cur + 1
        else
          rlen := rlen + 1; cur := cur - 1
          if cur < 0 && (-cur).toNat > back then back := (-cur).toNat
        if rlen < tot && rlen % lw == 0 && cfg.2.2 == q && 0 < cur then
          let P := (tot - rlen) / lw
          let D := back
          if D ≤ trail.length && cfg.1.take D == trail.take D then
            let r : RuleR Q := ⟨q, trail.take D, w, P, (cfg.1.drop D).take (P * lw), t⟩
            if r.Valid δ then return some r
  return none

/-- The same to the left: run `w^K | trail`, the head on the first cell of `trail`. -/
def learnL (q : Q) (trail w : List Bool) : Option (RuleL Q) := Id.run do
  let lw := w.length
  if lw == 0 || trail.isEmpty then return none
  let tot := KREP * lw
  let mut cfg : List Bool × List Bool × Q := (flat KREP w, trail, q)
  let mut llen := tot
  let mut t := 0
  let mut fwd : Nat := 0       -- how far right of the start the head has been
  let mut cur : Int := 0       -- head position relative to the start (right positive)
  while t < SCRATCH do
    match cfg.2.1 with
    | [] => return none
    | a :: _ =>
      let left := match δ cfg.2.2 a with
        | some (_, .L, _) => true
        | _ => false
      match bstep δ cfg with
      | none => return none
      | some c' =>
        cfg := c'
        t := t + 1
        if left then
          llen := llen - 1; cur := cur - 1
        else
          llen := llen + 1; cur := cur + 1
          if cur > 0 && cur.toNat > fwd then fwd := cur.toNat
        if llen < tot && llen % lw == 0 && cfg.2.2 == q && cur < 0 then
          let P := (tot - llen) / lw
          let D := fwd + 1
          if D ≤ trail.length && cfg.2.1.take D == trail.take D then
            let r : RuleL Q := ⟨q, trail.take D, w, P, (cfg.2.1.drop D).take (P * lw), t⟩
            if r.Valid δ then return some r
  return none

/-! ### The edges of the buffers -/

def TRAIL : Nat := 256
def KEEP : Nat := 64

/-- Rule tables and the state of the sampling. -/
structure Ctx (δ : Q → Bool → Option (Bool × Dir × Q)) [Hashable Q] where
  rD : Std.HashMap (Q × List Bool) (Array Nat) := {}
  rU : Std.HashMap (Q × List Bool × List Bool) (VRuleR δ) := {}
  lD : Std.HashMap (Q × List Bool) (Array Nat) := {}
  lU : Std.HashMap (Q × List Bool × List Bool) (VRuleL δ) := {}
  fails : Std.HashMap (Q × Bool × List Bool × List Bool) Unit := {}
  lastRight : Bool := true
  blankSeen : Bool := false
  tl : Nat := 0
  tsym : Bool := false
  travel : Nat := 48
  nlearn : Nat := 0
  nrule : Nat := 0
  nedge : Nat := 0
  nflush : Nat := 0
  nens : Nat := 0
  ntry : Nat := 0
  nu1 : Nat := 0
  nbig1 : Nat := 0
  keep : Nat := 64
  memo : Std.HashMap (List Bool) Side := {}
  nearLim : Nat := 8

inductive Ev
  | go
  | sample
  | halt
  | stuck
  | divfail (P : Nat)
  deriving Inhabited

variable [Hashable Q]

/-- Try the right rules in the table, in order. -/
def tryRulesR (rs : List (VRuleR δ)) (c : SCfg Q) : Except CrossFail (Mv δ c) :=
  match rs with
  | [] => .error .noMatch
  | r :: rs =>
    match mCrossR δ r c with
    | .ok mv => .ok mv
    | .error (.divides P) => .error (.divides P)
    | .error .noMatch => tryRulesR rs c

def tryRulesL (rs : List (VRuleL δ)) (c : SCfg Q) : Except CrossFail (Mv δ c) :=
  match rs with
  | [] => .error .noMatch
  | r :: rs =>
    match mCrossL δ r c with
    | .ok mv => .ok mv
    | .error (.divides P) => .error (.divides P)
    | .error .noMatch => tryRulesL rs c

/-- Enough copies for a crossing of `P` at a time to make progress. -/
def progress (n : Lin) (P : Nat) : Bool := !n.isK || decide (P ≤ n.a)

/-- The head at the start of the right rope (`rr = []`): a crossing, else one copy unrolled. -/
def edgeR (ctx : Ctx δ) (c : SCfg Q) : Ctx δ × Mv δ c × Ev :=
  match c.R with
  | [] => match mFetchR δ c with
    | some mv => (ctx, mv, .go)
    | none => (ctx, Mv.stay δ c, .stuck)
  | (w, n) :: _ =>
    if n.isZero then match mFetchR δ c with
      | some mv => (ctx, mv, .go)
      | none => (ctx, Mv.stay δ c, .stuck)
    else
    let ds := ctx.rD.getD (c.q, w) #[]
    let need := ds.foldl max 0
    let m1 := mEnsureL δ need 64 c
    let rs := ds.toList.filterMap (fun D => (ctx.rU.get? (c.q, w, m1.1.1.ll.take D)).filter (fun r => progress n r.1.P))
    match tryRulesR δ rs m1.1.1 with
    | .ok mv => ({ ctx with nrule := ctx.nrule + 1 }, m1.trans δ mv, .go)
    | .error (.divides P) => (ctx, m1, .divfail P)
    | .error .noMatch =>
      let c1 := m1.1.1
      let key := (c1.q, true, w, c1.ll.take 128)
      let tryLearn := (n.a ≥ 2 || !n.isK) && !(ctx.fails.contains key)
      let res : Option (Ctx δ × Mv δ c × Ev) := if !tryLearn then none else
        let m2 := mEnsureL δ TRAIL 64 c1
        let c2 := m2.1.1
        match learnR δ c2.q (c2.ll.take TRAIL) w with
        | none => none
        | some r =>
          if hv : r.Valid δ then
            let vr : VRuleR δ := ⟨r, hv⟩
            let ds := ctx.rD.getD (c.q, w) #[]
            let ctx' := { ctx with rD := ctx.rD.insert (c.q, w) (if ds.contains r.u.length then ds else ds.push r.u.length),
                                    rU := ctx.rU.insert (c.q, w, r.u) vr, nlearn := ctx.nlearn + 1 }
            if progress n r.P then
              match mCrossR δ vr c2 with
              | .ok mv => some ({ ctx' with nrule := ctx'.nrule + 1 }, m1.trans δ (m2.trans δ mv), .go)
              | .error (.divides P) => some (ctx', m1.trans δ m2, .divfail P)
              | .error .noMatch => none
            else none
          else none
      match res with
      | some r => r
      | none =>
        let ctx := if tryLearn then { ctx with fails := (if ctx.fails.size > 1000000 then {} else ctx.fails).insert key (), ntry := ctx.ntry + 1 } else ctx
        let ctx := { ctx with nu1 := ctx.nu1 + 1, nbig1 := ctx.nbig1 + (if isBig (w, n) then 1 else 0) }
        match mFetchAllR δ c1 with
        | some mv => (ctx, m1.trans δ mv, .go)
        | none => (ctx, m1, .stuck)

/-- The head at the start of the right buffer, the left buffer empty, the next move to the left. -/
def edgeL (ctx : Ctx δ) (c : SCfg Q) : Ctx δ × Mv δ c × Ev :=
  match c.L with
  | [] => match mFetchL δ c with
    | some mv => ({ ctx with blankSeen := true }, mv, .go)
    | none => (ctx, Mv.stay δ c, .stuck)
  | (w, n) :: _ =>
    if n.isZero then match mFetchL δ c with
      | some mv => (ctx, mv, .go)
      | none => (ctx, Mv.stay δ c, .stuck)
    else
    let ds := ctx.lD.getD (c.q, w) #[]
    let need := ds.foldl max 0
    let m1 := mEnsureR δ need 64 c
    let rs := ds.toList.filterMap (fun D => (ctx.lU.get? (c.q, w, m1.1.1.rr.take D)).filter (fun r => progress n r.1.P))
    match tryRulesL δ rs m1.1.1 with
    | .ok mv => ({ ctx with nrule := ctx.nrule + 1 }, m1.trans δ mv, .go)
    | .error (.divides P) => (ctx, m1, .divfail P)
    | .error .noMatch =>
      let c1 := m1.1.1
      let key := (c1.q, false, w, c1.rr.take 128)
      let tryLearn := (n.a ≥ 2 || !n.isK) && !(ctx.fails.contains key)
      let res : Option (Ctx δ × Mv δ c × Ev) := if !tryLearn then none else
        let m2 := mEnsureR δ TRAIL 64 c1
        let c2 := m2.1.1
        match learnL δ c2.q (c2.rr.take TRAIL) w with
        | none => none
        | some r =>
          if hv : r.Valid δ then
            let vr : VRuleL δ := ⟨r, hv⟩
            let ds := ctx.lD.getD (c.q, w) #[]
            let ctx' := { ctx with lD := ctx.lD.insert (c.q, w) (if ds.contains r.u.length then ds else ds.push r.u.length),
                                    lU := ctx.lU.insert (c.q, w, r.u) vr, nlearn := ctx.nlearn + 1 }
            if progress n r.P then
              match mCrossL δ vr c2 with
              | .ok mv => some ({ ctx' with nrule := ctx'.nrule + 1 }, m1.trans δ (m2.trans δ mv), .go)
              | .error (.divides P) => some (ctx', m1.trans δ m2, .divfail P)
              | .error .noMatch => none
            else none
          else none
      match res with
      | some r => r
      | none =>
        let ctx := if tryLearn then { ctx with fails := (if ctx.fails.size > 1000000 then {} else ctx.fails).insert key (), ntry := ctx.ntry + 1 } else ctx
        let ctx := { ctx with nu1 := ctx.nu1 + 1, nbig1 := ctx.nbig1 + (if isBig (w, n) then 1 else 0) }
        match mFetchAllL δ c1 with
        | some mv => (ctx, m1.trans δ mv, .go)
        | none => (ctx, m1, .stuck)

def CHUNK : Nat := 1 <<< 20

/-- One iteration: plain steps, then an edge (or a sample point, reported before the edge is crossed). -/
def iter (ctx : Ctx δ) (c : SCfg Q) : Ctx δ × Mv δ c × Ev :=
  let m := mPlain δ CHUNK c
  let c1 := m.1.1
  match c1.rr with
  | [] =>
    if !ctx.lastRight && (ctx.blankSeen || ctx.tsym || decide (ctx.travel ≤ ctx.tl)) then
      ({ ctx with lastRight := true, blankSeen := false, tl := 0, tsym := false }, m, .sample)
    else
      let m1 := if !(c1.ll.drop (2 * ctx.keep)).isEmpty then mFlushL δ (memoCF ctx.memo) ctx.keep ctx.nearLim c1 else Mv.stay δ c1
      let flushed := !(c1.ll.drop (2 * ctx.keep)).isEmpty
      let ctx := if flushed then { ctx with memo := recordSegs ctx.memo 12 m1.1.1.L } else ctx
      let r := edgeR δ { ctx with lastRight := true, tl := 0, tsym := false, nedge := ctx.nedge + 1, nflush := ctx.nflush + (if (c1.ll.drop (2 * ctx.keep)).isEmpty then 0 else 1), nens := ctx.nens + c1.ll.length } m1.1.1
      (r.1, m.trans δ (m1.trans δ r.2.1), r.2.2)
  | a :: _ =>
    match δ c1.q a with
    | none => (ctx, m, .halt)
    | some (_, .L, _) =>
      if c1.ll.isEmpty then
        let m1 := if !(c1.rr.drop (2 * ctx.keep)).isEmpty then mFlushR δ (memoCF ctx.memo) ctx.keep ctx.nearLim c1 else Mv.stay δ c1
        let flushed := !(c1.rr.drop (2 * ctx.keep)).isEmpty
        let ctx := if flushed then { ctx with memo := recordSegs ctx.memo 12 m1.1.1.R } else ctx
        let r := edgeL δ { ctx with lastRight := false, nedge := ctx.nedge + 1, nflush := ctx.nflush + (if (c1.rr.drop (2 * ctx.keep)).isEmpty then 0 else 1), nens := ctx.nens + c1.rr.length } m1.1.1
        let ctx2 := match m1.1.1.L with
          | (w, n) :: _ =>
            if r.1.nrule > ctx.nrule then { r.1 with tl := r.1.tl + w.length * n.a, tsym := r.1.tsym || !n.isK }
            else { r.1 with tl := r.1.tl + w.length }
          | [] => r.1
        (ctx2, m.trans δ (m1.trans δ r.2.1), r.2.2)
      else (ctx, m, .go)
    | some (_, .R, _) => (ctx, m, .go)

end Moves

/-! ## Jumps -/

def shiftSide (s : Side) : Side := s.map (fun it => (it.1, it.2.shift))
def shiftOKSide (s : Side) : Bool := s.all (fun it => decide (it.2.c ≤ it.2.a + it.2.b))
def instSide (v : Nat × Nat) (s : Side) : Side := s.map (fun it => (it.1, it.2.inst v))

theorem den_shiftSide (x y : Nat) : ∀ (s : Side), shiftOKSide s = true →
    den (x, y + 1) (shiftSide s) = den (x + 1, y) s
  | [], _ => rfl
  | (w, n) :: s, h => by
    simp only [shiftOKSide, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [shiftSide, List.map_cons, den_cons] at *
    rw [Lin.ev_shift x y n h.1]
    have := den_shiftSide x y s (by simpa [shiftOKSide] using h.2)
    simp only [shiftSide] at this
    rw [this]

theorem den_instSide (v w : Nat × Nat) : ∀ (s : Side), den w (instSide v s) = den v s
  | [] => rfl
  | (u, n) :: s => by
    simp only [instSide, List.map_cons, den_cons, Lin.ev_inst] at *
    rw [← den_instSide v w s]; rfl

def SCfg.shift (c : SCfg Q) : SCfg Q := ⟨shiftSide c.L, c.ll, c.rr, shiftSide c.R, c.q⟩
def SCfg.shiftOK (c : SCfg Q) : Bool := shiftOKSide c.L && shiftOKSide c.R
def SCfg.inst (v : Nat × Nat) (c : SCfg Q) : SCfg Q := ⟨instSide v c.L, c.ll, c.rr, instSide v c.R, c.q⟩

theorem SCfg.den_shift (x y : Nat) (c : SCfg Q) (h : c.shiftOK = true) : c.shift.den (x, y + 1) = c.den (x + 1, y) := by
  simp only [SCfg.shiftOK, Bool.and_eq_true] at h
  simp only [SCfg.shift, SCfg.den, den_shiftSide x y _ h.1, den_shiftSide x y _ h.2]

theorem SCfg.den_inst (v w : Nat × Nat) (c : SCfg Q) : (c.inst v).den w = c.den v := by
  simp only [SCfg.inst, SCfg.den, den_instSide]

/-- The steps of `y` periods from `(x, y)`. -/
def sumS (s : Lin) : Nat → Nat → Nat
  | _, 0 => 0
  | x, y + 1 => s.ev (x, y + 1) + sumS s (x + 1) y

theorem sumS_closed (s : Lin) : ∀ (y x : Nat),
    2 * sumS s x y + s.b * y = 2 * y * s.a + s.b * (2 * x * y + y * y) + s.c * (y * y + y)
  | 0, x => by simp [sumS]
  | y + 1, x => by
    have ih := sumS_closed s y (x + 1)
    simp only [sumS, Lin.ev]
    simp only [Nat.two_mul, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at ih ⊢
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] at ih ⊢
    omega

/-- The steps of `y` periods from `(0, y)`, in closed form. -/
def sumS0 (s : Lin) (y : Nat) : Nat := (2 * y * s.a + s.b * (y * y) + s.c * (y * y + y) - s.b * y) / 2

theorem sumS0_eq (s : Lin) (y : Nat) : sumS0 s y = sumS s 0 y := by
  have := sumS_closed s y 0
  simp only [Nat.mul_zero, Nat.zero_mul, Nat.zero_add] at this
  unfold sumS0
  omega

section
variable (δ : Q → Bool → Option (Bool × Dir × Q))

/-- **Jumps.** One period from `T` to `shift T`, proved for all values, gives `y` periods at once. -/
theorem jump_ok {T : SCfg Q} {s : Lin} (hT : OK δ T T.shift s) (hok : T.shiftOK = true) :
    ∀ (y x : Nat), steps δ (sumS s x y) (T.den (x, y)) = some (T.den (x + y, 0))
  | 0, x => by simp [sumS]
  | y + 1, x => by
    have h1 := hT (x, y + 1)
    rw [SCfg.den_shift x y T hok] at h1
    have h2 := jump_ok hT hok y (x + 1)
    rw [show x + 1 + y = x + (y + 1) by omega] at h2
    exact steps_seq δ h1 h2

end

/-! ## The run -/

section Run
variable [DecidableEq Q] [Hashable Q] (δ : Q → Bool → Option (Bool × Dir × Q))

structure Sample where
  sig : UInt64
  counts : Array Nat
  steps : Nat
  deriving Inhabited

/-- The words of a side with the counts of its small runs, and the counts of its big runs. -/
def sideShape (s : Side) : List (List Bool × Nat) × Array Nat :=
  s.foldr (fun it acc => if isBig it then ((it.1, 0) :: acc.1, acc.2.push it.2.a) else ((it.1, it.2.a + 1) :: acc.1, acc.2))
    ([], #[])

/-- The signature and the big counts of a canonical configuration (counts listed left rope first, nearest first,
then right rope, nearest first; `sideShape` collects them far end first, so they are reversed). -/
def shape (c : SCfg Q) : UInt64 × Array Nat :=
  let a := sideShape c.L
  let b := sideShape c.R
  (hash (c.q, c.ll, c.rr, a.1, b.1), a.2.reverse ++ b.2.reverse)

/-- Put the forms `fs` (from index `i`) as the counts of the big runs of a side. -/
def setBig (fs : Array Lin) : Side → Nat → Side × Nat
  | [], i => ([], i)
  | it :: s, i =>
    if isBig it then
      let r := setBig fs s (i + 1)
      ((it.1, fs.getD i it.2) :: r.1, r.2)
    else
      let r := setBig fs s i
      (it :: r.1, r.2)

def symCfg (c : SCfg Q) (fs : Array Lin) : SCfg Q :=
  let l := setBig fs c.L 0
  let r := setBig fs c.R l.2
  ⟨l.1, c.ll, c.rr, r.1, c.q⟩

/-- Run a family from `T` until a sample point where its canonical form is `target`. -/
def symRun (target T : SCfg Q) : Nat → Nat → Ctx δ → (c : SCfg Q) → (acc : Lin) → OK δ T c acc →
    Ctx δ × Option {s : Lin // OK δ T target s} × Nat
  | 0, _, ctx, _, _, _ => (ctx, none, 0)
  | f + 1, maxS, ctx, c, acc, h =>
    let r := iter δ ctx c
    let h1 := OK.trans δ h r.2.1.2
    match r.2.2 with
    | .go => symRun target T f maxS r.1 _ _ h1
    | .sample =>
      let mc := mCanon δ (memoCF r.1.memo) r.2.1.1.1
      let h2 := OK.trans δ h1 mc.2
      if heq : mc.1.1 = target then (r.1, some ⟨_, heq ▸ h2⟩, 0)
      else match maxS with
        | 0 => (r.1, none, 0)
        | m + 1 => symRun target T f m r.1 _ _ h2
    | .divfail P => (r.1, none, P)
    | _ => (r.1, none, 0)

def v0 : Nat × Nat := (0, 0)

/-- The state of a run from `start`: the configuration reached after `n` steps, proved. -/
structure RunSt (start : Cfg Q) where
  c : SCfg Q
  n : Nat
  h : steps δ n start = some (c.den v0)
  ctx : Ctx δ
  samples : Array Sample := #[]
  hist : Std.HashMap UInt64 (Array Nat) := {}
  njump : Nat := 0
  nsym : Nat := 0
  jfail : Nat := 0
  jumped : Nat := 0
  halted : Bool := false
  stuck : Bool := false

def MARGIN : Nat := 16

/-- A proposed jump `m` periods of `P` samples at a time, checked. -/
def tryJumpM {start : Cfg Q} (st : RunSt δ start) (P : Nat) (d : Array Int) (m : Nat) :
    Option (RunSt δ start) × Nat × Ctx δ :=
  let counts := (shape st.c).2
  -- the number of super-periods
  let Js := (List.range counts.size).filterMap (fun k =>
    let dk := d.getD k 0
    if dk < 0 then some ((counts.getD k 0 - MARGIN) / (m * dk.natAbs)) else none)
  match Js.min? with
  | none => (none, 0, st.ctx)
  | some J0 =>
    if J0 < 3 then (none, 0, st.ctx) else
    let J := J0 - 1
    let fs : Array Lin := (Array.range counts.size).map (fun k =>
      let ck := counts.getD k 0
      let dk := d.getD k 0
      if dk ≥ 0 then ⟨ck, m * dk.toNat, 0⟩ else ⟨ck - m * dk.natAbs * J, 0, m * dk.natAbs⟩)
    let T := symCfg st.c fs
    if hc : T.inst (0, J) = st.c then
      if hok : T.shiftOK = true then
        let r := symRun δ T.shift T 2000000 (2 * m * P + 4) st.ctx T (Lin.k 0) (OK.refl δ T)
        match r.2.1 with
        | none => (none, if r.2.2 = 0 then 1 else r.2.2 + 2, r.1)
        | some ⟨s, hs⟩ =>
          let h1 := jump_ok δ hs hok J 0
          let c' := T.inst (J, 0)
          have h2 : steps δ (st.n + sumS0 s J) start = some (c'.den v0) := by
            rw [sumS0_eq]
            have e1 : st.c.den v0 = T.den (0, J) := by rw [← hc, SCfg.den_inst]
            have e2 : c'.den v0 = T.den (0 + J, 0) := by simp [c', SCfg.den_inst]
            rw [e2]
            exact steps_seq δ st.h (e1 ▸ h1)
          let st' : RunSt δ start :=
            { c := c', n := st.n + sumS0 s J, h := h2, ctx := r.1, samples := #[], hist := {},
              njump := st.njump + 1, nsym := st.nsym, jfail := st.jfail, jumped := st.jumped + J * m * P }
          (some st', 1, r.1)
      else (none, 0, st.ctx)
    else (none, 0, st.ctx)

/-- Try `m = 1`, then multiples when a crossing needs the coefficients divisible by its period. -/
def tryJump {start : Cfg Q} (st : RunSt δ start) (P : Nat) (d : Array Int) : Nat → Nat → Option (RunSt δ start) × RunSt δ start
  | 0, _ => (none, st)
  | f + 1, m =>
    let r := tryJumpM δ st P d m
    let st := { st with ctx := r.2.2, nsym := st.nsym + (if r.2.1 = 0 then 0 else 1) }
    match r.1 with
    | some st' => (some { st' with nsym := st.nsym }, st)
    | none =>
      if r.2.1 ≤ 1 then (none, { st with jfail := st.jfail + r.2.1 })
      else
        let P' := r.2.1 - 2
        let m' := m * (P' / Nat.gcd m P')
        if m' = m || m' > 64 then (none, { st with jfail := st.jfail + 1 }) else tryJump st P d f m'

/-- At a sample point (the configuration canonical): record it, and look for a period with constant count changes
in the last samples (as rsim does); try a jump for each such period. -/
def sampleAndJump {start : Cfg Q} (st : RunSt δ start) : RunSt δ start := Id.run do
  let st := if st.samples.size ≥ 200000 then { st with samples := #[], hist := {} } else st
  let sh := shape st.c
  let sig := sh.1
  let counts := sh.2
  let idx := st.samples.size
  let samples := st.samples.push ⟨sig, counts, st.n⟩
  let prev := (st.hist.getD sig #[]).push idx
  let mut st := { st with samples := samples, hist := st.hist.insert sig prev }
  let np := prev.size
  let mut tried := 0
  for qq in [0:min (np - 1) 200] do
    let i := prev[np - 2 - qq]!
    let P := idx - i
    if 2 * P > idx then break
    let s2 := samples[idx - 2 * P]!
    let s1 := samples[idx - P]!
    if s2.sig != sig || s1.counts.size != counts.size || s2.counts.size != counts.size then continue
    let d : Array Int := (Array.range counts.size).map (fun k => Int.ofNat counts[k]! - Int.ofNat s1.counts[k]!)
    let d2 : Array Int := (Array.range counts.size).map (fun k => Int.ofNat s1.counts[k]! - Int.ofNat s2.counts[k]!)
    if d != d2 || d.all (· == 0) then continue
    if !((List.range P).all (fun t => samples[idx - t]!.sig == samples[idx - t - P]!.sig)) then continue
    tried := tried + 1
    if tried > 12 then break
    let r := tryJump δ st P d 6 1
    st := r.2
    match r.1 with
    | some st' => return st'
    | none => pure ()
  return st

/-- One iteration of the run. -/
def stepRun {start : Cfg Q} (st : RunSt δ start) : RunSt δ start :=
  let r := iter δ st.ctx st.c
  let h1 : steps δ (st.n + r.2.1.1.2.ev v0) start = some (r.2.1.1.1.den v0) := steps_seq δ st.h (r.2.1.2 v0)
  let st1 : RunSt δ start := { st with c := r.2.1.1.1, n := st.n + r.2.1.1.2.ev v0, h := h1, ctx := r.1 }
  match r.2.2 with
  | .go => st1
  | .sample =>
    let mc := mCanon δ (memoCF st1.ctx.memo) st1.c
    let h2 : steps δ (st1.n + mc.1.2.ev v0) start = some (mc.1.1.den v0) := steps_seq δ st1.h (mc.2 v0)
    let memo := recordSegs (recordSegs st1.ctx.memo 100000 mc.1.1.L) 100000 mc.1.1.R
    sampleAndJump δ { st1 with c := mc.1.1, n := st1.n + mc.1.2.ev v0, h := h2, ctx := { st1.ctx with memo := memo } }
  | .halt => { st1 with halted := true }
  | _ => { st1 with stuck := true }

/-- Run until `target` steps are reached, a halt, a stuck move, or the end of the fuel. -/
def runTo {start : Cfg Q} (target : Nat) : Nat → RunSt δ start → RunSt δ start
  | 0, st => st
  | f + 1, st => if target ≤ st.n || st.halted || st.stuck then st else runTo target f (stepRun δ st)

def init (q0 : Q) : RunSt δ (blankCfg q0) := { c := ⟨[], [], [], [], q0⟩, n := 0, h := rfl, ctx := {} }

/-- **Bounded run.** If the run reaches `N` steps, the machine makes `N` steps from blank tape without halting. -/
theorem run_ok (q0 : Q) (N fuel : Nat) (h : N ≤ (runTo δ N fuel (init δ q0)).n) :
    ∃ c, steps δ N (blankCfg q0) = some c := by
  have hh := (runTo δ N fuel (init δ q0)).h
  have e : (runTo δ N fuel (init δ q0)).n = N + ((runTo δ N fuel (init δ q0)).n - N) := by omega
  rw [e] at hh
  exact steps_le δ hh

end Run

end RS
end TM
