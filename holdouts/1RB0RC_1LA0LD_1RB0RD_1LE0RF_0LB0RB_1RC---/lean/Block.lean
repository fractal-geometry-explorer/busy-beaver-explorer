import Machine

/-!
# A block macro simulator, proved correct

The tape is cut into blocks of `K = 16` cells, kept as numbers (cell `i` of a block is bit `i`).  A table gives,
for every state, block and side of entry, what the machine does inside the block until the head leaves it: the
new block, the state, the side it leaves on and the number of steps (`mkEntry`, computed by `brun`, a run on the
block's cells that is proved to be a run of the machine whatever lies outside: `brun_ok`).  The macro simulator
`msim` looks up the table once per block crossing; `chkF_ok` turns a successful evaluation of it (followed by a few
single steps, `fsteps`) into a statement about `steps`.  The table is checked entry by entry inside `chkF`'s
hypothesis (`tblOk`), so nothing about the table has to be proved by hand.
-/

namespace H32641

open TM

/-! ## Runs inside a block -/

/-- Run on the cells `l` (left of the head, nearest first) and `x :: r` (the head on `x`) until the head leaves
them: `(true, l', s, n)` if it leaves to the right (`l'` the cells, nearest first), `(false, r', s, n)` if it leaves
to the left (`r'` the cells, left to right). -/
def brun : Nat → List Bool → List Bool → St → Option (Bool × List Bool × St × Nat)
  | 0, _, _, _ => none
  | _ + 1, _, [], _ => none
  | f + 1, l, x :: r, q =>
    match trans q x with
    | none => none
    | some (w, .R, s) =>
      match r with
      | [] => some (true, w :: l, s, 1)
      | y :: r' => (brun f (w :: l) (y :: r') s).map fun (d, c, s', n) => (d, c, s', n + 1)
    | some (w, .L, s) =>
      match l with
      | [] => some (false, w :: r, s, 1)
      | a :: l' => (brun f l' (a :: w :: r) s).map fun (d, c, s', n) => (d, c, s', n + 1)

/-- What a `brun` result says about the machine. -/
def BOk (l r : List Bool) (q : St) : Bool × List Bool × St × Nat → Prop
  | (true, c, s, n) => ∀ L R : Tape, steps n ⟨app l L, app r R, q⟩ = some ⟨app c L, R, s⟩
  | (false, c, s, n) => ∀ L R : Tape, steps n ⟨app l L, app r R, q⟩ = some ⟨tail L, cons (L 0) (app c R), s⟩

theorem steps_one {c c' : Config} (h : step c = some c') : steps 1 c = some c' := by
  simp [steps, TM.steps, h]

theorem brun_ok : ∀ (f : Nat) (l r : List Bool) (q : St) (o : Bool × List Bool × St × Nat),
    brun f l r q = some o → BOk l r q o := by
  intro f
  induction f with
  | zero => intro l r q o h; cases h
  | succ f ih =>
    intro l r q o h
    cases r with
    | nil => cases h
    | cons x r =>
      simp only [brun] at h
      cases e : trans q x with
      | none => rw [e] at h; cases h
      | some t =>
        obtain ⟨w, d, s⟩ := t
        rw [e] at h
        cases d with
        | R =>
          have hs : ∀ L R : Tape, step ⟨app l L, app (x :: r) R, q⟩ = some ⟨app (w :: l) L, app r R, s⟩ := by
            intro L R; simp [step, TM.step, e, app_cons]
          cases r with
          | nil =>
            simp only at h
            cases h
            intro L R
            exact steps_one (hs L R)
          | cons y r' =>
            simp only at h
            cases e2 : brun f (w :: l) (y :: r') s with
            | none => rw [e2] at h; cases h
            | some o' =>
              rw [e2] at h
              obtain ⟨d', c, s', n⟩ := o'
              cases h
              have h2 := ih _ _ _ _ e2
              cases d' with
              | true =>
                intro L R
                exact (steps_succ_of_step trans n (hs L R)).trans (h2 L R)
              | false =>
                intro L R
                exact (steps_succ_of_step trans n (hs L R)).trans (h2 L R)
        | L =>
          cases l with
          | nil =>
            have hs : ∀ L R : Tape, step ⟨app [] L, app (x :: r) R, q⟩ =
                some ⟨tail L, cons (L 0) (app (w :: r) R), s⟩ := by
              intro L R; simp [step, TM.step, e, app_cons]
            simp only at h
            cases h
            intro L R
            exact steps_one (hs L R)
          | cons a l' =>
            have hs : ∀ L R : Tape, step ⟨app (a :: l') L, app (x :: r) R, q⟩ =
                some ⟨app l' L, app (a :: w :: r) R, s⟩ := by
              intro L R; simp [step, TM.step, e, app_cons]
            simp only at h
            cases e2 : brun f l' (a :: w :: r) s with
            | none => rw [e2] at h; cases h
            | some o' =>
              rw [e2] at h
              obtain ⟨d', c, s', n⟩ := o'
              cases h
              have h2 := ih _ _ _ _ e2
              cases d' with
              | true =>
                intro L R
                exact (steps_succ_of_step trans n (hs L R)).trans (h2 L R)
              | false =>
                intro L R
                exact (steps_succ_of_step trans n (hs L R)).trans (h2 L R)

/-! ## Blocks -/

def K : Nat := 16

/-- The cells of a block, left to right. -/
def bits : Nat → Nat → List Bool
  | 0, _ => []
  | k + 1, b => (b % 2 == 1) :: bits k (b / 2)

def ofBits : List Bool → Nat
  | [] => 0
  | a :: l => (if a then 1 else 0) + 2 * ofBits l

theorem bits_length : ∀ k b, (bits k b).length = k := by
  intro k; induction k with
  | zero => intro b; rfl
  | succ k ih => intro b; simp [bits, ih]

theorem app_bits_zero : ∀ k, app (bits k 0) blank = blank := by
  intro k; induction k with
  | zero => rfl
  | succ k ih => simp only [bits, Nat.zero_mod, Nat.zero_div, app_cons, ih]; exact cons_false_blank

theorem app_rev_bits_zero (k : Nat) : app (bits k 0).reverse blank = blank := by
  have : (bits k 0).reverse = bits k 0 := by
    have h : ∀ k, bits k 0 = List.replicate k false := by
      intro k; induction k with
      | zero => rfl
      | succ k ih => simp [bits, ih, List.replicate_succ]
    rw [h, List.reverse_replicate]
  rw [this, app_bits_zero]

/-- Where the head starts in a block: on its first cell (entering from the left) or on its last. -/
def bstart (b : Nat) (side : Bool) : List Bool × List Bool :=
  if side then ([], bits K b) else ((bits K b).reverse.tail, [(bits K b).reverse.headD false])

structure Entry where
  q : St
  b : Nat
  side : Bool
  dir : Bool
  b' : Nat
  s : St
  n : Nat
  deriving DecidableEq, Repr

def FUEL : Nat := 4000

def mkEntry (q : St) (b : Nat) (side : Bool) : Option Entry :=
  match brun FUEL (bstart b side).1 (bstart b side).2 q with
  | some (true, c, s, n) =>
    let b' := ofBits c.reverse
    if (bits K b').reverse = c then some ⟨q, b, side, true, b', s, n⟩ else none
  | some (false, c, s, n) =>
    let b' := ofBits c
    if bits K b' = c then some ⟨q, b, side, false, b', s, n⟩ else none
  | none => none

def stIdx : St → Nat
  | .A => 0 | .B => 1 | .C => 2 | .D => 3 | .E => 4 | .F => 5

def stOf : Nat → St
  | 0 => .A | 1 => .B | 2 => .C | 3 => .D | 4 => .E | _ => .F

@[irreducible] def idx (q : St) (b : Nat) (side : Bool) : Nat := (stIdx q * 65536 + b) * 2 + (if side then 1 else 0)

/-- The table, one entry per state, block and side. -/
@[irreducible] def tbl : Array (Option Entry) :=
  Array.ofFn (n := 6 * 2 ^ K * 2) fun i => mkEntry (stOf (i.val / (2 * 2 ^ K))) (i.val / 2 % 2 ^ K) (i.val % 2 == 1)

def entryOk (o : Option Entry) : Bool :=
  match o with
  | none => true
  | some e => decide (mkEntry e.q e.b e.side = some e)

/-! ## Macro configurations -/

/-- Blocks left of the head (nearest first), blocks from the head on, state, and where the head is: on the first
cell of the first right block (`side = true`) or on the last cell of the first left block. -/
structure MC where
  Ls : List Nat
  Rs : List Nat
  q : St
  side : Bool
  deriving DecidableEq, Repr

def TL : List Nat → Tape
  | [] => blank
  | b :: l => app (bits K b).reverse (TL l)

def TR : List Nat → Tape
  | [] => blank
  | b :: l => app (bits K b) (TR l)

theorem TL_head (l : List Nat) : TL l = app (bits K (l.headD 0)).reverse (TL l.tail) := by
  cases l with
  | nil => simp only [TL, List.headD, List.tail]; rw [app_rev_bits_zero]
  | cons b l => rfl

theorem TR_head (l : List Nat) : TR l = app (bits K (l.headD 0)) (TR l.tail) := by
  cases l with
  | nil => simp only [TR, List.headD, List.tail]; rw [app_bits_zero]
  | cons b l => rfl

/-- The configuration a macro configuration stands for. -/
def sem (c : MC) : Config :=
  if c.side then ⟨TL c.Ls, TR c.Rs, c.q⟩
  else ⟨app (bits K (c.Ls.headD 0)).reverse.tail (TL c.Ls.tail),
        cons ((bits K (c.Ls.headD 0)).reverse.headD false) (TR c.Rs), c.q⟩

/-- After leaving a block on the left, the head is on the last cell of the next block. -/
theorem left_exit (Ls : List Nat) (X : Tape) (s : St) :
    (⟨tail (TL Ls), cons (TL Ls 0) X, s⟩ : Config) =
    ⟨app (bits K (Ls.headD 0)).reverse.tail (TL Ls.tail), cons ((bits K (Ls.headD 0)).reverse.headD false) X, s⟩ := by
  rw [TL_head Ls]
  have hl : (bits K (Ls.headD 0)).reverse.length = K := by rw [List.length_reverse, bits_length]
  generalize (bits K (Ls.headD 0)).reverse = rb at hl ⊢
  cases rb with
  | nil => simp [K] at hl
  | cons a t => rfl

/-- One macro step. -/
def next (c : MC) (e : Entry) : MC :=
  if c.side then
    if e.dir then ⟨e.b' :: c.Ls, c.Rs.tail, e.s, true⟩ else ⟨c.Ls, e.b' :: c.Rs.tail, e.s, false⟩
  else
    if e.dir then ⟨e.b' :: c.Ls.tail, c.Rs, e.s, true⟩ else ⟨c.Ls.tail, e.b' :: c.Rs, e.s, false⟩

/-- The block the head is in. -/
def cur (c : MC) : Nat := if c.side then c.Rs.headD 0 else c.Ls.headD 0

def mstep (T : Array (Option Entry)) (c : MC) : Option (Nat × MC) :=
  match T[idx c.q (cur c) c.side]? with
  | some (some e) => if e.q = c.q ∧ e.b = cur c ∧ e.side = c.side then some (e.n, next c e) else none
  | _ => none

theorem mkEntry_ok {q : St} {b : Nat} {side : Bool} {e : Entry} (h : mkEntry q b side = some e) :
    e.q = q ∧ e.b = b ∧ e.side = side ∧
    BOk (bstart b side).1 (bstart b side).2 q
      (e.dir, (if e.dir then (bits K e.b').reverse else bits K e.b'), e.s, e.n) := by
  unfold mkEntry at h
  cases e2 : brun FUEL (bstart b side).1 (bstart b side).2 q with
  | none => rw [e2] at h; cases h
  | some o =>
    rw [e2] at h
    obtain ⟨d, c, s, n⟩ := o
    have hb := brun_ok _ _ _ _ _ e2
    cases d with
    | true =>
      simp only at h
      split at h
      · rename_i hc; cases h; refine ⟨rfl, rfl, rfl, ?_⟩; simp only [ite_true]; rw [hc]; exact hb
      · cases h
    | false =>
      simp only at h
      split at h
      · rename_i hc; cases h; refine ⟨rfl, rfl, rfl, ?_⟩; simp only [Bool.false_eq_true, ite_false]; rw [hc]; exact hb
      · cases h

theorem mstep_ok {T : Array (Option Entry)} (hT : T.all entryOk = true) {c c' : MC} {n : Nat}
    (h : mstep T c = some (n, c')) :
    steps n (sem c) = some (sem c') := by
  unfold mstep at h
  cases eo : T[idx c.q (cur c) c.side]? with
  | none => rw [eo] at h; cases h
  | some o =>
    rw [eo] at h
    cases o with
    | none => cases h
    | some e =>
      simp only at h
      split at h
      · rename_i hk
        obtain ⟨hq, hb, hs⟩ := hk
        cases h
        have hmem := Array.mem_of_getElem? eo
        have hv := (Array.all_eq_true_iff_forall_mem.mp hT) _ hmem
        simp only [entryOk, decide_eq_true_eq] at hv
        obtain ⟨-, -, -, hok⟩ := mkEntry_ok hv
        rw [hq, hb, hs] at hok
        obtain ⟨Ls, Rs, q, side⟩ := c
        cases side with
        | true =>
          simp only [cur, bstart, ite_true] at hok
          simp only [sem, next, ite_true]
          rw [TR_head Rs]
          cases hd : e.dir with
          | true =>
            rw [hd] at hok
            simp only [BOk, ite_true] at hok
            have := hok (TL Ls) (TR Rs.tail)
            simp only [app_nil] at this
            simp only [ite_true]
            rw [this]; rfl
          | false =>
            rw [hd] at hok
            simp only [BOk, Bool.false_eq_true, ite_false] at hok
            have := hok (TL Ls) (TR Rs.tail)
            simp only [app_nil] at this
            simp only [Bool.false_eq_true, ite_false]
            rw [this, left_exit]; rfl
        | false =>
          simp only [cur, bstart, Bool.false_eq_true, ite_false] at hok
          simp only [sem, next, Bool.false_eq_true, ite_false]
          cases hd : e.dir with
          | true =>
            rw [hd] at hok
            simp only [BOk, ite_true] at hok
            have := hok (TL Ls.tail) (TR Rs)
            simp only [app_cons, app_nil] at this
            simp only [ite_true]
            rw [this]; rfl
          | false =>
            rw [hd] at hok
            simp only [BOk, Bool.false_eq_true, ite_false] at hok
            have := hok (TL Ls.tail) (TR Rs)
            simp only [app_cons, app_nil] at this
            simp only [Bool.false_eq_true, ite_false]
            rw [this, left_exit]; rfl
      · cases h

/-- Macro steps while they fit in the budget `rem`; returns the configuration and what is left of the budget. -/
def msim (T : Array (Option Entry)) : Nat → Nat → MC → MC × Nat
  | 0, rem, c => (c, rem)
  | f + 1, rem, c =>
    match mstep T c with
    | some (n, c') => if n ≤ rem then msim T f (rem - n) c' else (c, rem)
    | none => (c, rem)

theorem msim_ok {T : Array (Option Entry)} (hT : T.all entryOk = true) :
    ∀ (f rem : Nat) (c : MC), (msim T f rem c).2 ≤ rem ∧
      steps (rem - (msim T f rem c).2) (sem c) = some (sem (msim T f rem c).1) := by
  intro f
  induction f with
  | zero => intro rem c; simp [msim]
  | succ f ih =>
    intro rem c
    simp only [msim]
    cases e : mstep T c with
    | none => simp
    | some p =>
      obtain ⟨n, c'⟩ := p
      simp only
      split
      · rename_i hn
        obtain ⟨h1, h2⟩ := ih (rem - n) c'
        refine ⟨by omega, ?_⟩
        have h0 := mstep_ok hT e
        have := steps_seq trans h0 h2
        exact steps_congr trans (by omega) this
      · simp

/-! ## Back to lists -/

def fl (Ls : List Nat) : List Bool := Ls.flatMap fun b => (bits K b).reverse

def fr (Rs : List Nat) : List Bool := Rs.flatMap fun b => bits K b

theorem app_fl : ∀ Ls : List Nat, app (fl Ls) blank = TL Ls := by
  intro Ls; induction Ls with
  | nil => rfl
  | cons b l ih => simp only [fl, List.flatMap_cons] at *; rw [← app_app, ih]; rfl

theorem app_fr : ∀ Rs : List Nat, app (fr Rs) blank = TR Rs := by
  intro Rs; induction Rs with
  | nil => rfl
  | cons b l ih => simp only [fr, List.flatMap_cons] at *; rw [← app_app, ih]; rfl

/-- The list configuration of a macro configuration. -/
def toF (c : MC) : FCfg St :=
  if c.side then ⟨fl c.Ls, fr c.Rs, c.q⟩
  else ⟨(bits K (c.Ls.headD 0)).reverse.tail ++ fl c.Ls.tail,
        (bits K (c.Ls.headD 0)).reverse.headD false :: fr c.Rs, c.q⟩

theorem toF_ok (c : MC) : (toF c).toCfg = sem c := by
  obtain ⟨Ls, Rs, q, side⟩ := c
  cases side with
  | true => simp only [toF, sem, FCfg.toCfg, ite_true, app_fl, app_fr]
  | false =>
    simp only [toF, sem, FCfg.toCfg, Bool.false_eq_true, ite_false, app_cons]
    rw [← app_app, app_fl, app_fr]

/-! ## Data -/

def hexVal (c : Char) : Nat := if c.toNat ≤ 57 then c.toNat - 48 else c.toNat - 87

/-- Hex digits to cells, most significant bit first. -/
def hexCells (s : String) : List Bool :=
  s.toList.flatMap fun c =>
    let v := hexVal c
    [v / 8 % 2 == 1, v / 4 % 2 == 1, v / 2 % 2 == 1, v % 2 == 1]

def hexBlocksAux : List Char → List Nat
  | a :: b :: c :: d :: t => (((hexVal a * 16 + hexVal b) * 16 + hexVal c) * 16 + hexVal d) :: hexBlocksAux t
  | _ => []

/-- Four hex digits per block. -/
def hexBlocks (s : String) : List Nat := hexBlocksAux s.toList

/-- Drop trailing `false`s. -/
def strip : List Bool → List Bool
  | [] => []
  | a :: l => if strip l = [] ∧ a = false then [] else a :: strip l

theorem app_strip : ∀ l : List Bool, app (strip l) blank = app l blank := by
  intro l; induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [strip]
    split
    · rename_i h
      obtain ⟨h1, h2⟩ := h
      subst h2
      rw [app_cons, ← ih, h1]; exact cons_false_blank.symm
    · rw [app_cons, app_cons, ih]

/-- The check a chunk of the run is evaluated with: from `c`, exactly `t` steps (macro steps, then single steps)
end at `g`, up to trailing blank cells. -/
def chkF (T : Array (Option Entry)) (c : MC) (t : Nat) (g : FCfg St) : Bool :=
  let p := msim T t t c
  match fsteps p.2 (toF p.1) with
  | some f => strip f.l == strip g.l && strip f.r == strip g.r && f.st == g.st
  | none => false

theorem chkF_ok {T : Array (Option Entry)} (hT : T.all entryOk = true) {c : MC} {t : Nat} {g : FCfg St}
    (h : chkF T c t g = true) : steps t (sem c) = some g.toCfg := by
  unfold chkF at h
  obtain ⟨h1, h2⟩ := msim_ok hT t t c
  generalize msim T t t c = p at h h1 h2
  obtain ⟨c', rem⟩ := p
  simp only at h h1 h2
  cases e : fsteps rem (toF c') with
  | none => rw [e] at h; cases h
  | some f =>
    rw [e] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hl, hr⟩, hs⟩ := h
    have h3 := FCfg.steps_eq trans rem (toF c')
    have e' : TM.fsteps trans rem (toF c') = some f := e
    rw [e', toF_ok] at h3
    have hf : f.toCfg = g.toCfg := by
      unfold FCfg.toCfg
      rw [← app_strip f.l, ← app_strip f.r, hl, hr, hs, app_strip, app_strip]
    rw [Option.map_some, hf] at h3
    exact steps_congr trans (by omega) (steps_seq trans h2 h3)

end H32641
