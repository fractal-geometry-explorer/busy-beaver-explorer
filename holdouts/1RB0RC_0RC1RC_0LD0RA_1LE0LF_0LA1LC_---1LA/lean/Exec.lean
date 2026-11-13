import Machine

/-!
# A verified symbolic executor for 1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA

A configuration is two lists of tokens (nearest cell first on both sides, so the words of the left side are stored
reversed) and a state.  A token is a cell or a block: a word repeated `c + a₀ x₀ + a₁ x₁ + …` times, the `xᵢ` free.
`den ρ S` is the Turing-machine configuration that `S` stands for when `xᵢ = ρ i`.

One *move* of the executor (`move`) is

* a shift rule from a table (`crossWith`): a block next to the head is crossed in one go, with a carried word,
  one or two copies at a time (the count is divided, which must be possible for every value of the variables);
* otherwise one machine step (`stepS`); a block is opened only when its count is surely at least 1;
* and when that step brings state E to the left end of the tape, the right side is re-bracketed (`norm`) and a
  table of cycle rules is tried (`tryRules`): a rule is a template of the whole tape with counts `b₀ + 2 xᵢ` that
  comes back as the same template with counts `b₁ + 2 xᵢ`; it is applied N times at once.

Any step whose outcome would depend on a variable makes the executor return `none`.

The soundness theorem is `run_sound`: if `run T K S = some S'` and the tables are valid (`Tbl.OK`: each shift rule
is a statement about the machine for all surrounding tapes, each cycle rule is a statement for all values of its
variables), then for every `ρ` the machine goes from `den ρ S` to `den ρ S'`.  The executor's strategy (which rule,
how the tape is re-bracketed, how many times a rule is applied) is not trusted: every case of every function is
covered by the proof.  The Python model of this file is `py/replay/engine.py`.
-/

namespace H65826

open TM

/-! ## Reaching -/

/-- The machine goes from `c` to `c'` in some number of steps (without halting on the way). -/
def Reach (c c' : Config) : Prop := ∃ n, steps n c = some c'

theorem Reach.refl (c : Config) : Reach c c := ⟨0, rfl⟩

theorem Reach.trans {a b c : Config} (h₁ : Reach a b) (h₂ : Reach b c) : Reach a c := by
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, steps_seq H65826.trans hn hm⟩

/-! ## Counts -/

/-- The count `c + a₀ x₀ + a₁ x₁ + …`. -/
structure Cnt where
  c : Nat
  a : List Nat
  deriving DecidableEq, Repr

def dot : List Nat → (Nat → Nat) → Nat
  | [], _ => 0
  | a :: as, ρ => a * ρ 0 + dot as (fun i => ρ (i + 1))

def Cnt.eval (ρ : Nat → Nat) (n : Cnt) : Nat := n.c + dot n.a ρ

def addL : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x + y) :: addL xs ys

theorem dot_addL (xs ys : List Nat) (ρ : Nat → Nat) : dot (addL xs ys) ρ = dot xs ρ + dot ys ρ := by
  induction xs generalizing ys ρ with
  | nil => simp [addL, dot]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addL, dot]
    | cons y ys =>
      simp only [addL, dot, ih, Nat.add_mul]
      omega

def Cnt.add (m n : Cnt) : Cnt := ⟨m.c + n.c, addL m.a n.a⟩

theorem Cnt.eval_add (ρ : Nat → Nat) (m n : Cnt) : (m.add n).eval ρ = m.eval ρ + n.eval ρ := by
  simp only [Cnt.add, Cnt.eval, dot_addL]
  omega

/-- No variable occurs. -/
def Cnt.isConst (n : Cnt) : Bool := n.a.all (· == 0)

theorem dot_all_zero (as : List Nat) (ρ : Nat → Nat) (h : as.all (· == 0) = true) : dot as ρ = 0 := by
  induction as generalizing ρ with
  | nil => rfl
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp [dot, h.1, ih _ h.2]

theorem Cnt.eval_const (ρ : Nat → Nat) (n : Cnt) (h : n.isConst = true) : n.eval ρ = n.c := by
  simp [Cnt.eval, dot_all_zero n.a ρ h]

def Cnt.mul (k : Nat) (n : Cnt) : Cnt := ⟨k * n.c, n.a.map (k * ·)⟩

theorem dot_map_mul (k : Nat) (as : List Nat) (ρ : Nat → Nat) : dot (as.map (k * ·)) ρ = k * dot as ρ := by
  induction as generalizing ρ with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, dot, ih, Nat.mul_add, Nat.mul_assoc]

theorem Cnt.eval_mul (ρ : Nat → Nat) (k : Nat) (n : Cnt) : (n.mul k).eval ρ = k * n.eval ρ := by
  simp only [Cnt.mul, Cnt.eval, dot_map_mul, Nat.mul_add]

/-- `n = k * q + r` with `r` a number: possible when `k` divides every coefficient. -/
def Cnt.div (n : Cnt) (k : Nat) : Option (Cnt × Nat) :=
  if n.a.all (· % k == 0) then some (⟨n.c / k, n.a.map (· / k)⟩, n.c % k) else none

theorem dot_map_div (k : Nat) (as : List Nat) (ρ : Nat → Nat) (h : as.all (· % k == 0) = true) :
    dot as ρ = k * dot (as.map (· / k)) ρ := by
  induction as generalizing ρ with
  | nil => rfl
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    have e : a = k * (a / k) := by
      have := Nat.div_add_mod a k
      omega
    simp only [List.map_cons, dot, Nat.mul_add]
    rw [← ih _ h.2, ← Nat.mul_assoc, ← e]

theorem Cnt.eval_div (ρ : Nat → Nat) {n m : Cnt} {k r : Nat} (h : n.div k = some (m, r)) :
    n.eval ρ = k * m.eval ρ + r := by
  unfold Cnt.div at h
  split at h
  · rename_i ha
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Cnt.eval, Nat.mul_add]
    rw [← dot_map_div k n.a ρ ha]
    have := Nat.div_add_mod n.c k
    omega
  · cases h

/-! ## Tokens and their denotation -/

inductive Tok where
  | cell (b : Bool)
  | blk (w : List Bool) (n : Cnt)
  deriving DecidableEq, Repr

/-- The stream a token list stands for (nearest cell first; blank after the last token). -/
def dn (ρ : Nat → Nat) : List Tok → Tape
  | [] => blank
  | .cell b :: t => cons b (dn ρ t)
  | .blk w n :: t => rep (n.eval ρ) w (dn ρ t)

structure SCfg where
  l : List Tok
  r : List Tok
  st : St
  deriving DecidableEq, Repr

/-- The configuration `S` stands for at the values `ρ` of the variables. -/
def den (ρ : Nat → Nat) (S : SCfg) : Config := ⟨dn ρ S.l, dn ρ S.r, S.st⟩

theorem dn_cells (ρ : Nat → Nat) (w : List Bool) (t : List Tok) : dn ρ (w.map .cell ++ t) = app w (dn ρ t) := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [dn, ih]

/-- `w` written `k` times. -/
def wpow : Nat → List Bool → List Bool
  | 0, _ => []
  | k + 1, w => w ++ wpow k w

theorem app_wpow (k : Nat) (w : List Bool) (s : Tape) : app (wpow k w) s = rep k w s := by
  induction k with
  | zero => rfl
  | succ k ih => rw [wpow, ← app_app, ih]; rfl

theorem rep_wpow (m k : Nat) (w : List Bool) (s : Tape) : rep m (wpow k w) s = rep (k * m) w s := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have e : k * (m + 1) = k + k * m := by rw [Nat.mul_succ, Nat.add_comm]
    rw [rep_succ, ih, app_wpow, e, rep_add]

/-! ## Taking cells off a side, putting blocks on -/

/-- The nearest cell of a side and the rest.  A block is opened only if its count is surely at least 1. -/
def popCell : List Tok → Option (Bool × List Tok)
  | [] => some (false, [])
  | .cell b :: t => some (b, t)
  | .blk w n :: t =>
    match w with
    | [] => none
    | b :: w' =>
      if 1 ≤ n.c then
        some (b, w'.map .cell ++ (if n.c == 1 && n.isConst then t else .blk (b :: w') ⟨n.c - 1, n.a⟩ :: t))
      else none

theorem popCell_spec (ρ : Nat → Nat) {t t' : List Tok} {b : Bool} (h : popCell t = some (b, t')) :
    dn ρ t = cons b (dn ρ t') := by
  cases t with
  | nil =>
    simp only [popCell, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact cons_false_blank.symm
  | cons x t =>
    cases x with
    | cell c =>
      simp only [popCell, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | blk w n =>
      cases w with
      | nil => simp [popCell] at h
      | cons c w' =>
        simp only [popCell] at h
        split at h
        · rename_i hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [dn_cells]
          split
          · rename_i h1
            simp only [Bool.and_eq_true, beq_iff_eq] at h1
            have e : n.eval ρ = 1 := by rw [Cnt.eval_const ρ n h1.2]; exact h1.1
            simp only [dn, e]
            rfl
          · have e : n.eval ρ = (Cnt.eval ρ ⟨n.c - 1, n.a⟩) + 1 := by
              simp only [Cnt.eval]; omega
            simp only [dn, e]
            rfl
        · cases h

/-- Take the word `u` off a side, cell by cell. -/
def takeW : List Bool → List Tok → Option (List Tok)
  | [], t => some t
  | b :: u, t =>
    match popCell t with
    | some (b', t') => if b = b' then takeW u t' else none
    | none => none

theorem takeW_spec (ρ : Nat → Nat) {u : List Bool} {t t' : List Tok} (h : takeW u t = some t') :
    dn ρ t = app u (dn ρ t') := by
  induction u generalizing t with
  | nil =>
    simp only [takeW, Option.some.injEq] at h
    subst h
    rfl
  | cons b u ih =>
    simp only [takeW] at h
    split at h
    · rename_i b' t'' hp
      split at h
      · rename_i hb
        subst hb
        rw [popCell_spec ρ hp, ih h]
        rfl
      · cases h
    · cases h

/-- Put a block on a side; it merges with a block of the same word. -/
def pushBlk (w : List Bool) (n : Cnt) : List Tok → List Tok
  | .blk w' m :: t => if w = w' then .blk w (n.add m) :: t else .blk w n :: .blk w' m :: t
  | t => .blk w n :: t

theorem pushBlk_spec (ρ : Nat → Nat) (w : List Bool) (n : Cnt) (t : List Tok) :
    dn ρ (pushBlk w n t) = rep (n.eval ρ) w (dn ρ t) := by
  unfold pushBlk
  split
  · split
    · rename_i h
      subst h
      simp only [dn, Cnt.eval_add, rep_add]
    · rfl
  · rfl

/-! ## Shift rules -/

/-- A shift rule: in state `q`, with the word `u` carried on the side the head comes from, `k` copies of `w` are
crossed, leaving `v` behind; `s` steps.  All words nearest cell first. -/
structure SRule where
  q : St
  w : List Bool
  k : Nat
  u : List Bool
  v : List Bool
  s : Nat
  deriving Repr

/-- Valid as a rule for crossing to the right. -/
def SRule.OKR (r : SRule) : Prop :=
  ∀ L R : Tape, steps r.s ⟨app r.u L, app (wpow r.k r.w) R, r.q⟩ = some ⟨app r.u (app r.v L), R, r.q⟩

/-- Valid as a rule for crossing to the left. -/
def SRule.OKL (r : SRule) : Prop :=
  ∀ L R : Tape, steps r.s ⟨app (wpow r.k r.w) L, app r.u R, r.q⟩ = some ⟨L, app r.u (app r.v R), r.q⟩

/-- Cross the block `w^n` (already taken off its side, `far` is what is behind it) with the first rule of the list
that applies; `near` is the side the head comes from.  Returns the new `near` and `far`. -/
def crossWith (st : St) (w : List Bool) (n : Cnt) (near far : List Tok) :
    List SRule → Option (List Tok × List Tok)
  | [] => none
  | r :: rs =>
    if r.q = st ∧ r.w = w then
      match n.div r.k with
      | some (m, rem) =>
        if 1 ≤ m.c then
          match takeW r.u near with
          | some near' =>
            some (r.u.map .cell ++ pushBlk r.v m near', if rem = 0 then far else .blk w ⟨rem, []⟩ :: far)
          | none => crossWith st w n near far rs
        else crossWith st w n near far rs
      | none => crossWith st w n near far rs
    else crossWith st w n near far rs

theorem far_spec (ρ : Nat → Nat) (w : List Bool) (rem : Nat) (far : List Tok) :
    dn ρ (if rem = 0 then far else .blk w ⟨rem, []⟩ :: far) = rep rem w (dn ρ far) := by
  split
  · rename_i h; subst h; rfl
  · simp [dn, Cnt.eval, dot]

theorem crossWith_R (ρ : Nat → Nat) {st : St} {w : List Bool} {n : Cnt} {near far near' far' : List Tok}
    {rs : List SRule} (hrs : ∀ r ∈ rs, r.OKR) (h : crossWith st w n near far rs = some (near', far')) :
    Reach ⟨dn ρ near, rep (n.eval ρ) w (dn ρ far), st⟩ ⟨dn ρ near', dn ρ far', st⟩ := by
  induction rs with
  | nil => cases h
  | cons r rs ih =>
    have ih' := ih (fun r hr => hrs r (List.mem_cons_of_mem _ hr))
    simp only [crossWith] at h
    split at h
    · rename_i hq
      obtain ⟨hq, hw⟩ := hq
      split at h
      · rename_i m rem hd
        split at h
        · split at h
          · rename_i nr ht
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hr := hrs r (List.mem_cons_self ..)
            subst hw
            subst hq
            have hc := cross_r H65826.trans hr (m.eval ρ) (dn ρ nr) (rep rem r.w (dn ρ far))
            have e1 : dn ρ near = app r.u (dn ρ nr) := takeW_spec ρ ht
            have e2 := Cnt.eval_div ρ hd
            have e3 := far_spec ρ r.w rem far
            refine ⟨m.eval ρ * r.s, ?_⟩
            rw [e1, e2, e3, dn_cells, pushBlk_spec, rep_add, ← rep_wpow (m.eval ρ) r.k r.w]
            exact hc
          · exact ih' h
        · exact ih' h
      · exact ih' h
    · exact ih' h

theorem crossWith_L (ρ : Nat → Nat) {st : St} {w : List Bool} {n : Cnt} {near far near' far' : List Tok}
    {rs : List SRule} (hrs : ∀ r ∈ rs, r.OKL) (h : crossWith st w n near far rs = some (near', far')) :
    Reach ⟨rep (n.eval ρ) w (dn ρ far), dn ρ near, st⟩ ⟨dn ρ far', dn ρ near', st⟩ := by
  induction rs with
  | nil => cases h
  | cons r rs ih =>
    have ih' := ih (fun r hr => hrs r (List.mem_cons_of_mem _ hr))
    simp only [crossWith] at h
    split at h
    · rename_i hq
      obtain ⟨hq, hw⟩ := hq
      split at h
      · rename_i m rem hd
        split at h
        · split at h
          · rename_i nr ht
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hr := hrs r (List.mem_cons_self ..)
            subst hw
            subst hq
            have hc := cross_l H65826.trans hr (m.eval ρ) (rep rem r.w (dn ρ far)) (dn ρ nr)
            have e1 : dn ρ near = app r.u (dn ρ nr) := takeW_spec ρ ht
            have e2 := Cnt.eval_div ρ hd
            have e3 := far_spec ρ r.w rem far
            refine ⟨m.eval ρ * r.s, ?_⟩
            rw [e1, e2, e3, dn_cells, pushBlk_spec, rep_add, ← rep_wpow (m.eval ρ) r.k r.w]
            exact hc
          · exact ih' h
        · exact ih' h
      · exact ih' h
    · exact ih' h

/-- The smallest count a block must surely have to be crossed by a shift rule (a matter of strategy only). -/
def minCross : Nat := 6

/-- Cross the block under the head (to the right), or else the block just left of the head (to the left). -/
def cross (shR shL : List SRule) (S : SCfg) : Option SCfg :=
  let a : Option SCfg :=
    match S.r with
    | .blk w n :: far =>
      if minCross ≤ n.c then
        match crossWith S.st w n S.l far shR with
        | some (l, r) => some ⟨l, r, S.st⟩
        | none => none
      else none
    | _ => none
  match a with
  | some S' => some S'
  | none =>
    match S.l with
    | .blk w n :: far =>
      if minCross ≤ n.c then
        match crossWith S.st w n S.r far shL with
        | some (r, l) => some ⟨l, r, S.st⟩
        | none => none
      else none
    | _ => none

theorem cross_sound (ρ : Nat → Nat) {shR shL : List SRule} (hR : ∀ r ∈ shR, r.OKR) (hL : ∀ r ∈ shL, r.OKL)
    {S S' : SCfg} (h : cross shR shL S = some S') : Reach (den ρ S) (den ρ S') := by
  obtain ⟨l, r, st⟩ := S
  simp only [cross] at h
  split at h
  · rename_i S'' ha
    simp only [Option.some.injEq] at h
    subst h
    split at ha
    · rename_i w n far
      split at ha
      · split at ha
        · rename_i l' r' hc
          simp only [Option.some.injEq] at ha
          subst ha
          exact crossWith_R ρ hR hc
        · cases ha
      · cases ha
    · cases ha
  · split at h
    · rename_i w n far
      split at h
      · split at h
        · rename_i r' l' hc
          simp only [Option.some.injEq] at h
          subst h
          exact crossWith_L ρ hL hc
        · cases h
      · cases h
    · cases h

/-! ## One machine step -/

def stepS (S : SCfg) : Option SCfg :=
  match popCell S.r with
  | none => none
  | some (b, r') =>
    match trans S.st b with
    | none => none
    | some (wr, .R, q) => some ⟨.cell wr :: S.l, r', q⟩
    | some (wr, .L, q) =>
      match popCell S.l with
      | none => none
      | some (a, l') => some ⟨l', .cell a :: .cell wr :: r', q⟩

theorem stepS_sound (ρ : Nat → Nat) {S S' : SCfg} (h : stepS S = some S') :
    steps 1 (den ρ S) = some (den ρ S') := by
  obtain ⟨l, r, st⟩ := S
  simp only [stepS] at h
  split at h
  · cases h
  · rename_i b r' hp
    have hr := popCell_spec ρ hp
    split at h
    · cases h
    · rename_i wr q ht
      simp only [Option.some.injEq] at h
      subst h
      have hs : TM.step H65826.trans (den ρ ⟨l, r, st⟩) = some (den ρ ⟨.cell wr :: l, r', q⟩) := by
        simp only [den, TM.step, hr, cons_zero, ht, tail_cons, dn]
      exact steps_succ_of_step H65826.trans 0 hs
    · rename_i wr q ht
      split at h
      · cases h
      · rename_i a l' hl
        simp only [Option.some.injEq] at h
        subst h
        have hl' := popCell_spec ρ hl
        have hs : TM.step H65826.trans (den ρ ⟨l, r, st⟩) = some (den ρ ⟨l', .cell a :: .cell wr :: r', q⟩) := by
          simp only [den, TM.step, hr, hl', cons_zero, ht, tail_cons, dn]
        exact steps_succ_of_step H65826.trans 0 hs

/-! ## Re-bracketing a side -/

/-- The cells of `w`, as cells, at the front of a token list. -/
def stripCells : List Bool → List Tok → Option (List Tok)
  | [], t => some t
  | b :: w, .cell b' :: t => if b = b' then stripCells w t else none
  | _ :: _, _ => none

theorem stripCells_spec (ρ : Nat → Nat) {w : List Bool} {t t' : List Tok} (h : stripCells w t = some t') :
    dn ρ t = app w (dn ρ t') := by
  induction w generalizing t with
  | nil =>
    simp only [stripCells, Option.some.injEq] at h
    subst h
    rfl
  | cons b w ih =>
    cases t with
    | nil => simp [stripCells] at h
    | cons x t =>
      cases x with
      | cell b' =>
        simp only [stripCells] at h
        split at h
        · rename_i hb
          subst hb
          simp only [dn, ih h, app_cons]
        · cases h
      | blk w' n => simp [stripCells] at h

/-- A block absorbs blocks of the same word and literal copies of its word that follow it. -/
def absorb : Nat → List Bool → Cnt → List Tok → Cnt × List Tok
  | 0, _, n, rest => (n, rest)
  | f + 1, w, n, rest =>
    let a : Option (Cnt × List Tok) :=
      match rest with
      | .blk w' m :: rest' => if w' = w then some (n.add m, rest') else none
      | _ => none
    match a with
    | some (n', r') => absorb f w n' r'
    | none =>
      match stripCells w rest with
      | some r' => absorb f w ⟨n.c + 1, n.a⟩ r'
      | none => (n, rest)

theorem absorb_spec (ρ : Nat → Nat) (f : Nat) (w : List Bool) (n : Cnt) (rest : List Tok) :
    rep ((absorb f w n rest).1.eval ρ) w (dn ρ (absorb f w n rest).2) = rep (n.eval ρ) w (dn ρ rest) := by
  induction f generalizing n rest with
  | zero => rfl
  | succ f ih =>
    simp only [absorb]
    split
    · rename_i n' r' ha
      rw [ih]
      split at ha
      · split at ha
        · rename_i w' m rest' hw
          simp only [Option.some.injEq, Prod.mk.injEq] at ha
          obtain ⟨rfl, rfl⟩ := ha
          subst hw
          simp only [dn, Cnt.eval_add, rep_add]
        · cases ha
      · cases ha
    · split
      · rename_i r' hs
        rw [ih, stripCells_spec ρ hs, rep_app_comm]
        have e : Cnt.eval ρ ⟨n.c + 1, n.a⟩ = n.eval ρ + 1 := by simp only [Cnt.eval]; omega
        rw [e]
      · rfl

/-- The shortest `d` with `w = d^j`, found by trying every length (the answer is checked where it is used). -/
def rootOf (w : List Bool) : List Bool × Nat :=
  let rec go (fuel d : Nat) : List Bool × Nat :=
    match fuel with
    | 0 => (w, 1)
    | fuel + 1 =>
      if d < w.length then
        if w.length % d == 0 && wpow (w.length / d) (w.take d) == w then (w.take d, w.length / d)
        else go fuel (d + 1)
      else (w, 1)
  go w.length 1

/-- A block with its word reduced to its root. -/
def rootRed (w : List Bool) (n : Cnt) : List Bool × Cnt :=
  let dj := rootOf w
  if decide (1 < dj.2) && wpow dj.2 dj.1 == w then (dj.1, n.mul dj.2) else (w, n)

theorem rootRed_spec (ρ : Nat → Nat) (w : List Bool) (n : Cnt) (s : Tape) :
    rep ((rootRed w n).2.eval ρ) (rootRed w n).1 s = rep (n.eval ρ) w s := by
  simp only [rootRed]
  split
  · rename_i hok
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    rw [Cnt.eval_mul, ← rep_wpow, hok.2]
  · rfl

/-- A word as its last cell and what is before it. -/
def unsnoc : List Bool → Option (List Bool × Bool)
  | [] => none
  | a :: t =>
    match unsnoc t with
    | none => some ([], a)
    | some (d, b) => some (a :: d, b)

theorem unsnoc_spec {w d : List Bool} {b : Bool} (h : unsnoc w = some (d, b)) : w = d ++ [b] := by
  induction w generalizing d with
  | nil => cases h
  | cons a t ih =>
    simp only [unsnoc] at h
    split at h
    · rename_i hn
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases t with
      | nil => rfl
      | cons c t =>
        simp only [unsnoc] at hn
        split at hn <;> cases hn
    · rename_i d' b' hs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [ih hs]
      rfl

mutual
/-- Put a cell in front of a token list: a block whose word ends in that cell is rotated to the left of it. -/
def cellOnto : Nat → Bool → List Tok → List Tok
  | 0, b, rest => .cell b :: rest
  | f + 1, b, rest =>
    match rest with
    | .blk w n :: rest' =>
      match unsnoc w with
      | some (d, b') => if b' = b then blkOnto f (b :: d) n (cellOnto f b rest') else .cell b :: rest
      | none => .cell b :: rest
    | _ => .cell b :: rest
/-- Put a block in front of a token list: its word is reduced to its root, it absorbs what follows, and a block of
fewer than three copies is written out. -/
def blkOnto : Nat → List Bool → Cnt → List Tok → List Tok
  | 0, w, n, rest => .blk w n :: rest
  | f + 1, w, n, rest =>
    let wn := rootRed w n
    let nr := absorb (rest.length + 1) wn.1 wn.2 rest
    if nr.1.isConst && decide (nr.1.c < 3) then
      (wpow nr.1.c wn.1).foldr (fun b acc => cellOnto f b acc) nr.2
    else .blk wn.1 nr.1 :: nr.2
end

theorem onto_spec (ρ : Nat → Nat) (f : Nat) :
    (∀ b rest, dn ρ (cellOnto f b rest) = cons b (dn ρ rest)) ∧
    (∀ w n rest, dn ρ (blkOnto f w n rest) = rep (n.eval ρ) w (dn ρ rest)) := by
  induction f with
  | zero => exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  | succ f ih =>
    obtain ⟨ihc, ihb⟩ := ih
    constructor
    · intro b rest
      simp only [cellOnto]
      split
      · rename_i w n rest'
        split
        · rename_i d b' hu
          split
          · rename_i hb
            subst hb
            rw [ihb, ihc]
            have e := unsnoc_spec hu
            have r := rep_rotate (n.eval ρ) [b'] w (b' :: d) (by rw [e]; simp) (dn ρ rest')
            simp only [dn]
            exact r.symm
          · rfl
        · rfl
      · rfl
    · intro w n rest
      simp only [blkOnto]
      rw [← rootRed_spec ρ w n, ← absorb_spec ρ (rest.length + 1)]
      generalize rootRed w n = wn
      generalize absorb (rest.length + 1) wn.1 wn.2 rest = nr
      split
      · rename_i hsmall
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hsmall
        rw [Cnt.eval_const ρ _ hsmall.1, ← app_wpow]
        generalize wpow nr.1.c wn.1 = cells
        induction cells with
        | nil => rfl
        | cons c cells ihl => simp only [List.foldr_cons, ihc, ihl, app_cons]
      · rfl

def normFuel : Nat := 100000

/-- One pass from the far end: every token is put in front of the normal form of what follows it. -/
def npass (t : List Tok) : List Tok :=
  t.foldr (fun tok acc =>
    match tok with
    | .cell b => cellOnto normFuel b acc
    | .blk w n => blkOnto normFuel w n acc) []

theorem npass_spec (ρ : Nat → Nat) (t : List Tok) : dn ρ (npass t) = dn ρ t := by
  induction t with
  | nil => rfl
  | cons x t ih =>
    have ih' : dn ρ (List.foldr (fun tok acc =>
        match tok with
        | .cell b => cellOnto normFuel b acc
        | .blk w n => blkOnto normFuel w n acc) [] t) = dn ρ t := ih
    cases x with
    | cell b => simp only [npass, List.foldr_cons, (onto_spec ρ normFuel).1, ih', dn]
    | blk w n => simp only [npass, List.foldr_cons, (onto_spec ρ normFuel).2, ih', dn]

/-- The cells at the front of a token list. -/
def leadCells : List Tok → List Bool
  | .cell b :: t => b :: leadCells t
  | _ => []

/-- How many times `w` is found at the front of `s`, one copy after the other. -/
def countCopies (w : List Bool) : Nat → List Bool → Nat
  | 0, _ => 0
  | f + 1, s => if w.isPrefixOf s then 1 + countCopies w f (s.drop w.length) else 0

/-- A word of at most 14 cells of which at least four copies start `s`, covering the most cells (strategy only). -/
def bestRepeat (s : List Bool) : Option (List Bool × Nat) :=
  (List.range 14).foldl (fun best i =>
    let lw := i + 1
    let w := s.take lw
    let c := 1 + countCopies w s.length (s.drop lw)
    let better : Bool :=
      match best with
      | none => true
      | some (w', c') => decide (c' * w'.length < c * lw)
    if decide (4 ≤ c) && better then some (w, c) else best) none

/-- Runs of four or more equal words among the cells become blocks. -/
def form : Nat → List Tok → List Tok
  | 0, t => t
  | _ + 1, [] => []
  | f + 1, .blk w n :: t => .blk w n :: form f t
  | f + 1, .cell b :: t =>
    match bestRepeat (b :: leadCells t) with
    | some (w, c) =>
      match stripCells (wpow c w) (.cell b :: t) with
      | some t' => .blk w ⟨c, []⟩ :: form f t'
      | none => .cell b :: form f t
    | none => .cell b :: form f t

theorem form_spec (ρ : Nat → Nat) (f : Nat) (t : List Tok) : dn ρ (form f t) = dn ρ t := by
  induction f generalizing t with
  | zero => rfl
  | succ f ih =>
    cases t with
    | nil => rfl
    | cons x t =>
      cases x with
      | blk w n => simp only [form, dn, ih]
      | cell b =>
        simp only [form]
        split
        · rename_i w c _
          split
          · rename_i t' hs
            rw [stripCells_spec ρ hs, app_wpow]
            simp [dn, ih, Cnt.eval, dot]
          · simp only [dn, ih]
        · simp only [dn, ih]

/-- The normal form of a side. -/
def norm (t : List Tok) : List Tok :=
  npass (form normFuel (npass (form normFuel (npass (form normFuel (npass t))))))

theorem norm_spec (ρ : Nat → Nat) (t : List Tok) : dn ρ (norm t) = dn ρ t := by
  simp only [norm, npass_spec, form_spec]

/-! ## Cycle rules -/

/-- A token of a rule's template: a cell, a block with a fixed count, or a block whose count is `b0 + 2 x` before
and `b1 + 2 x` after one application (`x` free). -/
inductive TT where
  | cell (b : Bool)
  | fix (w : List Bool) (n : Nat)
  | var (w : List Bool) (b0 b1 : Nat)
  deriving DecidableEq, Repr

/-- The template as tokens, the variable of a block being its position in the list (`sel = false`: before,
`true`: after). -/
def symK (sel : Bool) : Nat → List TT → List Tok
  | _, [] => []
  | k, .cell b :: t => .cell b :: symK sel (k + 1) t
  | k, .fix w n :: t => .blk w ⟨n, []⟩ :: symK sel (k + 1) t
  | k, .var w b0 b1 :: t => .blk w ⟨if sel then b1 else b0, List.replicate k 0 ++ [2]⟩ :: symK sel (k + 1) t

/-- A cycle rule, as a statement about the machine: from the template with counts `b0 + 2 xᵢ` (state E at the left
end, nothing to its left) the machine reaches the template with counts `b1 + 2 xᵢ`, for all values of the `xᵢ`. -/
def RuleOK (t : List TT) : Prop :=
  ∀ ρ : Nat → Nat, Reach ⟨blank, dn ρ (symK false 0 t), .E⟩ ⟨blank, dn ρ (symK true 0 t), .E⟩

/-- Before and after have the same parity in every block. -/
def wfT : List TT → Bool
  | [] => true
  | .var _ b0 b1 :: t => b0 % 2 == b1 % 2 && wfT t
  | _ :: t => wfT t

/-- The template with the count of the block at position `i` equal to `min b0 b1 + 2 ρ i`. -/
def instV : List TT → (Nat → Nat) → Tape
  | [], _ => blank
  | .cell b :: t, ρ => cons b (instV t (fun i => ρ (i + 1)))
  | .fix w n :: t, ρ => rep n w (instV t (fun i => ρ (i + 1)))
  | .var w b0 b1 :: t, ρ => rep (min b0 b1 + 2 * ρ 0) w (instV t (fun i => ρ (i + 1)))

/-- By position: half of what a block's count before (`sel = false`) or after is above `min b0 b1`. -/
def uvec (sel : Bool) : List TT → Nat → Nat
  | [], _ => 0
  | .var _ b0 b1 :: _, 0 => ((if sel then b1 else b0) - min b0 b1) / 2
  | _ :: _, 0 => 0
  | _ :: t, i + 1 => uvec sel t i

theorem dot_replicate (k : Nat) (ρ : Nat → Nat) : dot (List.replicate k 0 ++ [2]) ρ = 2 * ρ k := by
  induction k generalizing ρ with
  | zero => simp [dot]
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, dot, ih]
    omega

theorem sym_inst (ρ : Nat → Nat) (sel : Bool) (t : List TT) (k : Nat) (hw : wfT t = true) :
    dn ρ (symK sel k t) = instV t (fun i => ρ (k + i) + uvec sel t i) := by
  induction t generalizing k with
  | nil => rfl
  | cons e t ih =>
    have tl : ∀ e', (fun i => ρ (k + (i + 1)) + uvec sel (e' :: t) (i + 1)) =
        (fun i => ρ (k + 1 + i) + uvec sel t i) := by
      intro e'
      funext i
      have : k + (i + 1) = k + 1 + i := by omega
      rw [this]
      cases e' <;> rfl
    cases e with
    | cell b =>
      simp only [symK, dn, instV]
      rw [ih (k + 1) hw, tl]
    | fix w n =>
      simp only [symK, dn, instV]
      rw [ih (k + 1) hw, tl]
      simp [Cnt.eval, dot]
    | var w b0 b1 =>
      simp only [wfT, Bool.and_eq_true, beq_iff_eq] at hw
      simp only [symK, dn, instV]
      rw [ih (k + 1) hw.2, tl]
      have e : Cnt.eval ρ ⟨if sel = true then b1 else b0, List.replicate k 0 ++ [2]⟩ =
          min b0 b1 + 2 * (ρ (k + 0) + uvec sel (.var w b0 b1 :: t) 0) := by
        simp only [Cnt.eval, dot_replicate, uvec, Nat.add_zero]
        cases sel <;> simp <;> omega
      rw [e]

theorem rule_inst {t : List TT} (ht : RuleOK t) (hw : wfT t = true) (ρ : Nat → Nat) :
    Reach ⟨blank, instV t (fun i => ρ i + uvec false t i), .E⟩ ⟨blank, instV t (fun i => ρ i + uvec true t i), .E⟩ := by
  have h := ht ρ
  rw [sym_inst ρ false t 0 hw, sym_inst ρ true t 0 hw] at h
  simpa using h

theorem rule_instN {t : List TT} (ht : RuleOK t) (hw : wfT t = true) (N : Nat) : ∀ ρ : Nat → Nat,
    Reach ⟨blank, instV t (fun i => ρ i + N * uvec false t i), .E⟩
      ⟨blank, instV t (fun i => ρ i + N * uvec true t i), .E⟩ := by
  induction N with
  | zero =>
    intro ρ
    simp only [Nat.zero_mul, Nat.add_zero]
    exact Reach.refl _
  | succ N ih =>
    intro ρ
    have h1 := rule_inst ht hw (fun i => ρ i + N * uvec false t i)
    have h2 := ih (fun i => ρ i + uvec true t i)
    have e1 : (fun i => ρ i + (N + 1) * uvec false t i) = (fun i => ρ i + N * uvec false t i + uvec false t i) := by
      funext i; rw [Nat.succ_mul]; omega
    have e2 : (fun i => ρ i + N * uvec false t i + uvec true t i) =
        (fun i => ρ i + uvec true t i + N * uvec false t i) := by
      funext i; omega
    have e3 : (fun i => ρ i + uvec true t i + N * uvec true t i) = (fun i => ρ i + (N + 1) * uvec true t i) := by
      funext i; rw [Nat.succ_mul]; omega
    rw [e1]
    rw [e2] at h1
    rw [e3] at h2
    exact h1.trans h2

/-- One token of the tape against one token of the template, for N applications at once. -/
def appTok (N : Nat) : TT → Tok → Option Tok
  | .cell b, .cell b' => if b = b' then some (.cell b') else none
  | .fix w n, .blk w' m => if w = w' ∧ m.isConst = true ∧ m.c = n then some (.blk w' m) else none
  | .var w b0 b1, .blk w' m =>
    if w = w' ∧ b0 % 2 = b1 % 2 ∧ m.a.all (· % 2 == 0) = true ∧
        min b0 b1 + 2 * (N * ((b0 - min b0 b1) / 2)) ≤ m.c ∧ (m.c - min b0 b1) % 2 = 0 then
      some (.blk w' ⟨m.c - 2 * (N * ((b0 - min b0 b1) / 2)) + 2 * (N * ((b1 - min b0 b1) / 2)), m.a⟩)
    else none
  | _, _ => none

def appToks (N : Nat) : List TT → List Tok → Option (List Tok)
  | [], [] => some []
  | e :: t, x :: s =>
    match appTok N e x, appToks N t s with
    | some x', some s' => some (x' :: s')
    | _, _ => none
  | _, _ => none

theorem dot_even (as : List Nat) (ρ : Nat → Nat) (h : as.all (· % 2 == 0) = true) : dot as ρ % 2 = 0 := by
  rw [dot_map_div 2 as ρ h]
  omega

theorem app_inst (ρ : Nat → Nat) (N : Nat) (t : List TT) : ∀ (toks toks' : List Tok),
    appToks N t toks = some toks' →
    ∃ ρ' : Nat → Nat, dn ρ toks = instV t (fun i => ρ' i + N * uvec false t i) ∧
      dn ρ toks' = instV t (fun i => ρ' i + N * uvec true t i) := by
  induction t with
  | nil =>
    intro toks toks' h
    cases toks with
    | nil =>
      simp only [appToks, Option.some.injEq] at h
      subst h
      exact ⟨fun _ => 0, rfl, rfl⟩
    | cons x s => simp [appToks] at h
  | cons e t ih =>
    intro toks toks' h
    cases toks with
    | nil => simp [appToks] at h
    | cons x s =>
      simp only [appToks] at h
      split at h
      · rename_i x' s' hx hs
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨ρt, h1, h2⟩ := ih s s' hs
        cases e with
        | cell b =>
          cases x with
          | cell b' =>
            simp only [appTok] at hx
            split at hx
            · rename_i hb
              simp only [Option.some.injEq] at hx
              subst hx
              subst hb
              refine ⟨fun i => match i with | 0 => 0 | i + 1 => ρt i, ?_, ?_⟩
              · simp only [dn, instV, h1, uvec]
              · simp only [dn, instV, h2, uvec]
            · cases hx
          | blk w' m => simp [appTok] at hx
        | fix w n =>
          cases x with
          | cell b' => simp [appTok] at hx
          | blk w' m =>
            simp only [appTok] at hx
            split at hx
            · rename_i hc
              obtain ⟨hw, hcst, hn⟩ := hc
              simp only [Option.some.injEq] at hx
              subst hx
              subst hw
              have e : m.eval ρ = n := by rw [Cnt.eval_const ρ m hcst]; exact hn
              refine ⟨fun i => match i with | 0 => 0 | i + 1 => ρt i, ?_, ?_⟩
              · simp only [dn, instV, h1, uvec, e]
              · simp only [dn, instV, h2, uvec, e]
            · cases hx
        | var w b0 b1 =>
          cases x with
          | cell b' => simp [appTok] at hx
          | blk w' m =>
            simp only [appTok] at hx
            split at hx
            · rename_i hc
              obtain ⟨hw, hpar, hev, hge, hmod⟩ := hc
              simp only [Option.some.injEq] at hx
              subst hx
              subst hw
              have hd := dot_even m.a ρ hev
              generalize hA0 : N * ((b0 - min b0 b1) / 2) = A0 at hge
              generalize hA1 : N * ((b1 - min b0 b1) / 2) = A1
              refine ⟨fun i => match i with
                | 0 => (m.c + dot m.a ρ - min b0 b1 - 2 * A0) / 2
                | i + 1 => ρt i, ?_, ?_⟩
              · simp only [dn, instV, h1, uvec, Bool.false_eq_true, ite_false, hA0, Cnt.eval]
                congr 1
                omega
              · simp only [dn, instV, h2, uvec, ite_true, hA1, Cnt.eval]
                congr 1
                omega
            · cases hx
      · cases h

/-- The number of applications that fit: the smallest count over the shrinking blocks decides (strategy only;
`appToks` checks). -/
def ruleN : List TT → List Tok → Option Nat
  | .var _ b0 b1 :: t, .blk _ m :: s =>
    let r := ruleN t s
    if b1 < b0 then
      let k := (m.c - b0) / (b0 - b1) + 1
      some (match r with | none => k | some k' => min k k')
    else r
  | _ :: t, _ :: s => ruleN t s
  | _, _ => none

def tryRule (t : List TT) (toks : List Tok) : Option (List Tok) :=
  match ruleN t toks with
  | some N => if 1 ≤ N then appToks N t toks else none
  | none => none

def tryRules : List (List TT) → List Tok → Option (List Tok)
  | [], _ => none
  | t :: rs, toks =>
    match tryRule t toks with
    | some r => some r
    | none => tryRules rs toks

theorem tryRule_sound (ρ : Nat → Nat) {t : List TT} (ht : RuleOK t) (hw : wfT t = true) {toks toks' : List Tok}
    (h : tryRule t toks = some toks') : Reach ⟨blank, dn ρ toks, .E⟩ ⟨blank, dn ρ toks', .E⟩ := by
  simp only [tryRule] at h
  split at h
  · rename_i N _
    split at h
    · obtain ⟨ρ', h1, h2⟩ := app_inst ρ N t toks toks' h
      rw [h1, h2]
      exact rule_instN ht hw N ρ'
    · cases h
  · cases h

theorem tryRules_sound (ρ : Nat → Nat) {rs : List (List TT)} (hrs : ∀ t ∈ rs, RuleOK t ∧ wfT t = true)
    {toks toks' : List Tok} (h : tryRules rs toks = some toks') :
    Reach ⟨blank, dn ρ toks, .E⟩ ⟨blank, dn ρ toks', .E⟩ := by
  induction rs with
  | nil => cases h
  | cons t rs ih =>
    simp only [tryRules] at h
    split at h
    · rename_i r hr
      simp only [Option.some.injEq] at h
      subst h
      have := hrs t (List.mem_cons_self ..)
      exact tryRule_sound ρ this.1 this.2 hr
    · exact ih (fun t ht => hrs t (List.mem_cons_of_mem _ ht)) h

/-! ## The executor -/

/-- The tables: shift rules to the right and to the left, cycle rules. -/
structure Tbl where
  shR : List SRule
  shL : List SRule
  rules : List (List TT)

structure Tbl.OK (T : Tbl) : Prop where
  shR : ∀ r ∈ T.shR, r.OKR
  shL : ∀ r ∈ T.shL, r.OKL
  rules : ∀ t ∈ T.rules, RuleOK t ∧ wfT t = true

/-- At an event (state E at the left end): normal form, then the first cycle rule that applies. -/
def atEvent (T : Tbl) (S : SCfg) : SCfg :=
  let r := norm S.r
  match tryRules T.rules r with
  | some r' => ⟨S.l, r', S.st⟩
  | none => ⟨S.l, r, S.st⟩

def move (T : Tbl) (S : SCfg) : Option SCfg :=
  match cross T.shR T.shL S with
  | some S' => some S'
  | none =>
    match stepS S with
    | none => none
    | some S' => if S'.st = .E ∧ S'.l = [] then some (atEvent T S') else some S'

theorem atEvent_sound (ρ : Nat → Nat) {T : Tbl} (hT : T.OK) {S : SCfg} (hs : S.st = .E) (hl : S.l = []) :
    Reach (den ρ S) (den ρ (atEvent T S)) := by
  obtain ⟨l, r, st⟩ := S
  simp only at hs hl
  subst hs
  subst hl
  simp only [atEvent]
  split
  · rename_i r' hr
    have := tryRules_sound ρ hT.rules hr
    rw [norm_spec] at this
    exact this
  · simp only [den, norm_spec]
    exact Reach.refl _

theorem move_sound (ρ : Nat → Nat) {T : Tbl} (hT : T.OK) {S S' : SCfg} (h : move T S = some S') :
    Reach (den ρ S) (den ρ S') := by
  simp only [move] at h
  split at h
  · rename_i S'' hc
    simp only [Option.some.injEq] at h
    subst h
    exact cross_sound ρ hT.shR hT.shL hc
  · split at h
    · cases h
    · rename_i S'' hst
      have h1 : Reach (den ρ S) (den ρ S'') := ⟨1, stepS_sound ρ hst⟩
      split at h
      · rename_i hev
        simp only [Option.some.injEq] at h
        subst h
        exact h1.trans (atEvent_sound ρ hT hev.1 hev.2)
      · simp only [Option.some.injEq] at h
        subst h
        exact h1

/-- `k` moves. -/
def run (T : Tbl) : Nat → SCfg → Option SCfg
  | 0, S => some S
  | k + 1, S =>
    match move T S with
    | none => none
    | some S' => run T k S'

/-- **Soundness of the executor.**  With valid tables, whatever the executor does in `k` moves the machine does in
some number of steps, for every value of the variables. -/
theorem run_sound {T : Tbl} (hT : T.OK) (k : Nat) {S S' : SCfg} (h : run T k S = some S') (ρ : Nat → Nat) :
    Reach (den ρ S) (den ρ S') := by
  induction k generalizing S with
  | zero =>
    simp only [run, Option.some.injEq] at h
    subst h
    exact Reach.refl _
  | succ k ih =>
    simp only [run] at h
    split at h
    · cases h
    · rename_i S'' hm
      exact (move_sound ρ hT hm).trans (ih h)

/-- A run whose first move is a machine step takes at least one step. -/
theorem run_pos {T : Tbl} (hT : T.OK) (k : Nat) {S S' : SCfg} (hc : cross T.shR T.shL S = none)
    (h : run T (k + 1) S = some S') (ρ : Nat → Nat) : ∃ n, 0 < n ∧ steps n (den ρ S) = some (den ρ S') := by
  simp only [run] at h
  split at h
  · cases h
  · rename_i S₁ hm
    obtain ⟨m, hm'⟩ := run_sound hT k h ρ
    simp only [move, hc] at hm
    split at hm
    · cases hm
    · rename_i S₂ hst
      have h1 := stepS_sound ρ hst
      have h2 : Reach (den ρ S₂) (den ρ S₁) := by
        split at hm
        · rename_i hev
          simp only [Option.some.injEq] at hm
          subst hm
          exact atEvent_sound ρ hT hev.1 hev.2
        · simp only [Option.some.injEq] at hm
          subst hm
          exact Reach.refl _
      obtain ⟨j, hj⟩ := h2
      exact ⟨1 + j + m, by omega, steps_seq H65826.trans (steps_seq H65826.trans h1 hj) hm'⟩

/-- A cycle rule proved by the executor: a run from the template before to the template after. -/
theorem ruleOK_of_run {T : Tbl} (hT : T.OK) (k : Nat) {t : List TT}
    (h : run T k ⟨[], symK false 0 t, .E⟩ = some ⟨[], symK true 0 t, .E⟩) : RuleOK t :=
  fun ρ => run_sound hT k h ρ

end H65826
