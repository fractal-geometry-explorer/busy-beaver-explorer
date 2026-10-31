import Macro

/-!
# The recursive pass: the last block a multiple of 3

When the last block is `3j + 3` the converter does not stop at the left end of the block (`k_start`): it carries on
into the blocks to the left, and what it leaves behind is no longer a block of ones but a row of short words.  This
file follows that with a machine on lists of numbers, `astep`, and proves every one of its steps sound for the real
machine (`astep_sound`, kernel only).  The configurations are

  `enc ⟨q, h, L, W⟩  =  … 0 1^{L_1} 0 1^{L_0} q> 1^h 0 1^{W_0} 0 1^{W_1} … 0^∞`

with `L` the blocks to the left, nearest first, each followed outward by a 0 (blocks of length 0 allowed, missing
blocks at the far end count as 0), and `W` the words to the right, each `0 1^k` (`rt`).  `arun` iterates `astep`
until the pass is over, and `pass` is the whole pass map: `next` from `Macro.lean` when the last block is not a
multiple of 3, `arun` from `k_start` when it is.  `pass_sound`: whatever `pass` says, the machine does.
-/

namespace BB6c

open TM

/-- The words to the right of the head, each `0 1^k`, then blank tape. -/
def rt : List Nat → Tape
  | [] => blank
  | k :: W => cons false (rep k [true] (rt W))

/-- `k` blocks of length 0. -/
def zs (k : Nat) (L : List Nat) : List Nat := List.replicate k 0 ++ L

/-- Words `0 1^a`, then `j` words `0 1 1`, the last of all `k` longer. -/
def tw (a : Nat) : Nat → Nat → List Nat
  | 0, k => [a + k]
  | j + 1, k => a :: tw 2 j k

/-- A configuration of the block machine: state, ones under and right of the head, blocks left, words right. -/
structure ACfg where
  q : St
  h : Nat
  L : List Nat
  W : List Nat
  deriving DecidableEq

def enc (c : ACfg) : Config := ⟨lt c.L, rep c.h [true] (rt c.W), c.q⟩

/-- The first `n` blocks made explicit, missing ones as 0. -/
def pad : Nat → List Nat → List Nat
  | 0, L => L
  | n + 1, L => L.headD 0 :: pad n L.tail

theorem lt_pad (n : Nat) : ∀ L : List Nat, lt (pad n L) = lt L := by
  induction n with
  | zero => intro L; rfl
  | succ n ih =>
    intro L
    show rep (L.headD 0) [true] (cons false (lt (pad n L.tail))) = lt L
    rw [ih]
    cases L with
    | nil => exact cons_false_blank
    | cons _ _ => rfl

theorem zcomm (k : Nat) (s : Tape) : cons false (rep k [false] s) = rep k [false] (cons false s) :=
  (rep_app_comm k [false] s).symm

theorem lt_zs (k : Nat) (L : List Nat) : lt (zs k L) = rep k [false] (lt L) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show cons false (lt (zs k L)) = cons false (rep k [false] (lt L))
    rw [ih]

/-- A block `1` and `k` empty blocks in front of `L`. -/
theorem lt_one_zs (k : Nat) (L : List Nat) :
    lt (1 :: zs k L) = cons true (rep k [false] (cons false (lt L))) := by
  show cons true (cons false (lt (zs k L))) = _
  rw [lt_zs, zcomm]

theorem rt_tw (a j k : Nat) (W : List Nat) :
    rt (tw a j k ++ W) = cons false (rep a [true] (rep j [false, true, true] (rep k [true] (rt W)))) := by
  induction j generalizing a with
  | zero => show cons false (rep (a + k) [true] (rt W)) = _; rw [ones_add]; rfl
  | succ j ih => show cons false (rep a [true] (rt (tw 2 j k ++ W))) = _; rw [ih]; rfl

theorem ones_three (j r : Nat) (s : Tape) : rep (3 * j + r) [true] s = rep j [true, true, true] (rep r [true] s) := by
  induction j with
  | zero => rw [Nat.mul_zero, Nat.zero_add]; rfl
  | succ j ih => rw [show 3 * (j + 1) + r = 3 + (3 * j + r) by omega, ones_add, ih]; rfl

/-- What one step of the block machine leads to. -/
inductive Out where
  | go : ACfg → Out
  | pass : List Nat → Nat → Out
  | halt : Out
  deriving DecidableEq

/-- What `Out` promises about the real machine, from `x`. -/
def Leads (x : Config) : Out → Prop
  | .go c' => Reaches x (enc c')
  | .pass ls n => Reaches x (K ls n)
  | .halt => TM.Halts trans x

theorem Leads.trans {x y : Config} {o : Out} (h₁ : Reaches x y) (h₂ : Leads y o) : Leads x o := by
  cases o with
  | go _ => exact h₁.trans h₂
  | pass _ _ => exact h₁.trans h₂
  | halt =>
    obtain ⟨n₁, h₁⟩ := h₁
    obtain ⟨n₂, c'', h₂, h₃⟩ := h₂
    exact ⟨n₁ + n₂, c'', steps_seq BB6c.trans h₁ h₂, h₃⟩

/-! ## The steps, one by one -/

theorem s_a_run (h a : Nat) (M W : List Nat) :
    Reaches (enc ⟨.A, h, a :: M, W⟩) (enc ⟨.A, 0, (a + h) :: M, W⟩) := by
  have e := ra_run h (lt (a :: M)) (rt W)
  rw [show lt (a :: M) = rep a [true] (cons false (lt M)) from rfl, ← ones_add, Nat.add_comm] at e
  exact reaches_of e

theorem s_a_end (n : Nat) (M : List Nat) : Reaches (enc ⟨.A, 0, (n + 1) :: M, []⟩) (K M n) :=
  reaches_of (start n (lt M))

theorem s_a_tok (k : Nat) (L W : List Nat) :
    Reaches (enc ⟨.A, 0, L, (k + 1) :: W⟩) (enc ⟨.B, 0, 1 :: zs k L, W⟩) := by
  have e := ra_tok k (lt L) (rt W)
  unfold enc; rw [lt_one_zs]; exact reaches_of e

theorem s_d_halt (L : List Nat) : TM.Halts trans (enc ⟨.D, 0, L, []⟩) := ⟨1, _, rfl, rfl⟩

theorem s_d_one (a : Nat) (M W : List Nat) : Reaches (enc ⟨.D, 0, a :: M, 1 :: W⟩) (enc ⟨.D, 0, (a + 2) :: M, W⟩) :=
  reaches_of (rd_one a (lt M) (rt W))

theorem s_d_two (a : Nat) (M W : List Nat) :
    Reaches (enc ⟨.D, 0, a :: M, 2 :: W⟩) (enc ⟨.F, 0, 0 :: (a + 2) :: M, W⟩) :=
  reaches_of (rd_two a (lt M) (rt W))

theorem s_d_tok (k a : Nat) (M W : List Nat) :
    Reaches (enc ⟨.D, 0, a :: M, (k + 3) :: W⟩) (enc ⟨.B, 0, 1 :: zs k ((a + 2) :: M), W⟩) := by
  have e := rd_tok k a (lt M) (rt W)
  unfold enc; rw [lt_one_zs]; exact reaches_of e

theorem s_e_halt (L : List Nat) : TM.Halts trans (enc ⟨.E, 1, L, []⟩) := ⟨2, _, rfl, rfl⟩

theorem s_e_one (a : Nat) (M W : List Nat) : Reaches (enc ⟨.E, 1, a :: M, 1 :: W⟩) (enc ⟨.D, 0, (a + 3) :: M, W⟩) :=
  reaches_of (re_one a (lt M) (rt W))

theorem s_e_two (a : Nat) (M W : List Nat) :
    Reaches (enc ⟨.E, 1, a :: M, 2 :: W⟩) (enc ⟨.F, 0, 0 :: (a + 3) :: M, W⟩) :=
  reaches_of (re_two a (lt M) (rt W))

theorem s_e_tok (k a : Nat) (M W : List Nat) :
    Reaches (enc ⟨.E, 1, a :: M, (k + 3) :: W⟩) (enc ⟨.B, 0, 1 :: zs k ((a + 3) :: M), W⟩) := by
  have e := re_tok k a (lt M) (rt W)
  unfold enc; rw [lt_one_zs]; exact reaches_of e

theorem s_f_tok (k a : Nat) (M W : List Nat) :
    Reaches (enc ⟨.F, 0, a :: M, k :: W⟩) (enc ⟨.A, 0, (a + k + 1) :: M, W⟩) := by
  have e := rf_tok k a (lt M) (rt W)
  rw [ones_cons, ← ones_add, show k + 1 + a = a + k + 1 by omega] at e
  exact reaches_of e

theorem s_f_end (a : Nat) (M : List Nat) : Reaches (enc ⟨.F, 0, a :: M, []⟩) (K M a) :=
  (reaches_of (n := 1) rfl).trans (reaches_of (start a (lt M)))

theorem s_c_tok (c k : Nat) (M W : List Nat) :
    Reaches (enc ⟨.C, 0, (c + 1) :: M, k :: W⟩) (enc ⟨.B, 0, 1 :: zs k (c :: M), W⟩) := by
  have e := rc_tok c k (lt M) (rt W)
  unfold enc; rw [lt_one_zs]; exact reaches_of e

theorem s_c_one (d : Nat) (M W : List Nat) :
    Reaches (enc ⟨.C, 0, 0 :: d :: M, 1 :: W⟩) (enc ⟨.F, 0, 0 :: (d + 2) :: M, W⟩) :=
  reaches_of (rc_one d (lt M) (rt W))

theorem s_c_more (d k : Nat) (M W : List Nat) :
    Reaches (enc ⟨.C, 0, 0 :: d :: M, (k + 2) :: W⟩) (enc ⟨.B, 0, 1 :: zs k ((d + 2) :: M), W⟩) := by
  have e := rc_more d k (lt M) (rt W)
  unfold enc; rw [lt_one_zs]; exact reaches_of e

theorem s_b_end (x y : Nat) (M : List Nat) :
    Reaches (enc ⟨.B, 0, 1 :: 0 :: y :: x :: M, []⟩) (K ((x + 2) :: M) (y + 1)) := by
  have e := y_end x y (lt M)
  rw [blk2] at e
  exact reaches_of e

theorem s_b_one (c j k : Nat) (M W : List Nat) :
    Reaches (enc ⟨.B, 0, (3 * j + 1) :: c :: M, k :: W⟩) (enc ⟨.B, 0, c :: M, 0 :: (tw 1 j k ++ W)⟩) := by
  have e := rb_one c j k (lt M) (rt W)
  unfold enc lt; simp only [rt, rep_zero]; rw [ones_three, rt_tw]; exact reaches_of e

theorem s_b_two (c j k : Nat) (M W : List Nat) :
    Reaches (enc ⟨.B, 0, (3 * j + 5) :: c :: M, k :: W⟩) (enc ⟨.E, 1, (c + 3) :: M, tw 2 j k ++ W⟩) := by
  have e := rb_two c j k (lt M) (rt W)
  unfold enc lt; simp only [rt, rep_zero]; rw [ones_three, rt_tw]; exact reaches_of e

theorem s_b_two0 (c k : Nat) (M W : List Nat) :
    Reaches (enc ⟨.B, 0, 2 :: c :: M, k :: W⟩) (enc ⟨.E, k + 1, (c + 3) :: M, W⟩) :=
  reaches_of (rb_two0 c k (lt M) (rt W))

theorem s_b_zero (c j : Nat) (M W : List Nat) :
    Reaches (enc ⟨.B, 0, (3 * j) :: c :: M, 0 :: W⟩) (enc ⟨.C, 0, c :: M, tw 1 j 0 ++ W⟩) := by
  have e := rb_zero c j (lt M) (rt W)
  unfold enc lt; simp only [rt, rep_zero]; rw [show 3 * j = 3 * j + 0 from rfl, ones_three, rt_tw]
  exact reaches_of e

theorem s_b_empty (c k : Nat) (M W : List Nat) :
    Reaches (enc ⟨.B, 0, 0 :: c :: M, (k + 1) :: W⟩) (enc ⟨.C, 0, c :: M, (k + 2) :: W⟩) :=
  reaches_of (rb_empty c k (lt M) (rt W))

theorem s_b_three0 (c d k : Nat) (M W : List Nat) :
    Reaches (enc ⟨.B, 0, 3 :: c :: d :: M, (k + 1) :: W⟩) (enc ⟨.A, k + 2, (c + 2) :: (d + 2) :: M, W⟩) := by
  have e := rb_three c d 0 k (lt M) (rt W)
  rw [blk2] at e
  exact reaches_of e

theorem s_b_three (c d j k : Nat) (M W : List Nat) :
    Reaches (enc ⟨.B, 0, (3 * j + 6) :: c :: d :: M, (k + 1) :: W⟩)
      (enc ⟨.A, 1, (c + 2) :: (d + 2) :: M, tw 2 j (k + 1) ++ W⟩) := by
  have e := rb_three c d (j + 1) k (lt M) (rt W)
  rw [blk2] at e
  unfold enc lt; rw [show 3 * j + 6 = 3 * (j + 1) + 3 by omega, ones_three, rt_tw]; exact reaches_of e

theorem s_k_start (c j : Nat) (M : List Nat) :
    Reaches (K (c :: M) (3 * j + 2)) (enc ⟨.B, 0, c :: M, 0 :: 1 :: tw 2 j 0⟩) := by
  have e := k_start c j (lt M)
  rw [show rep j [true, false, true] (cons true blank) = cons true (rep j [false, true, true] blank) from
    (rep_rotate j [true] [false, true, true] [true, false, true] rfl blank).symm] at e
  unfold K enc; rw [ones_three, ← List.append_nil (tw 2 j 0)]; simp only [rt, rep_zero]; rw [rt_tw]
  exact reaches_of e

/-- C after a block `c` before the words `0 1` and `0 1^k`: the block moves into the second word, three steps of the
block machine per cell. -/
theorem s_c_move (k : Nat) (M W : List Nat) : ∀ c : Nat,
    Reaches (enc ⟨.C, 0, c :: M, 1 :: k :: W⟩) (enc ⟨.C, 0, 0 :: M, 1 :: (k + c) :: W⟩)
  | 0 => ⟨0, rfl⟩
  | c + 1 => by
    have h₁ := s_c_tok c 1 M (k :: W)
    have h₂ := s_b_one 0 0 k (c :: M) W
    have h₃ := s_b_zero c 0 M ((1 + k) :: W)
    have h₄ := s_c_move (1 + k) M W c
    rw [show 1 + k + c = k + (c + 1) by omega] at h₄
    exact h₁.trans (h₂.trans (h₃.trans h₄))

/-! ## The block machine -/

/-- The converter `B` at a block `n` with blocks `c`, `d` to its left, before a word `0 1^k`. -/
def bstep (n c d : Nat) (M : List Nat) (k : Nat) (W : List Nat) : Option Out :=
  if n % 3 = 1 then some (.go ⟨.B, 0, c :: d :: M, 0 :: (tw 1 (n / 3) k ++ W)⟩)
  else if n = 2 then some (.go ⟨.E, k + 1, (c + 3) :: d :: M, W⟩)
  else if n % 3 = 2 then some (.go ⟨.E, 1, (c + 3) :: d :: M, tw 2 (n / 3 - 1) k ++ W⟩)
  else if k = 0 then some (.go ⟨.C, 0, c :: d :: M, tw 1 (n / 3) 0 ++ W⟩)
  else if n = 0 then some (.go ⟨.C, 0, c :: d :: M, (k + 1) :: W⟩)
  else if n = 3 then some (.go ⟨.A, k + 1, (c + 2) :: (d + 2) :: M, W⟩)
  else some (.go ⟨.A, 1, (c + 2) :: (d + 2) :: M, tw 2 (n / 3 - 2) k ++ W⟩)

/-- One step of the block machine, on a configuration whose first four blocks are explicit; `none` where it is not
covered (none of these occur in the runs checked). -/
def astep' : St → Nat → List Nat → List Nat → Option Out
  | .A, h + 1, a :: M, W => some (.go ⟨.A, 0, (a + h + 1) :: M, W⟩)
  | .A, 0, (n + 1) :: M, [] => some (.pass M n)
  | .A, 0, L, (k + 1) :: W => some (.go ⟨.B, 0, 1 :: zs k L, W⟩)
  | .D, 0, _, [] => some .halt
  | .D, 0, a :: M, 1 :: W => some (.go ⟨.D, 0, (a + 2) :: M, W⟩)
  | .D, 0, a :: M, 2 :: W => some (.go ⟨.F, 0, 0 :: (a + 2) :: M, W⟩)
  | .D, 0, a :: M, (k + 3) :: W => some (.go ⟨.B, 0, 1 :: zs k ((a + 2) :: M), W⟩)
  | .E, 1, _, [] => some .halt
  | .E, 1, a :: M, 1 :: W => some (.go ⟨.D, 0, (a + 3) :: M, W⟩)
  | .E, 1, a :: M, 2 :: W => some (.go ⟨.F, 0, 0 :: (a + 3) :: M, W⟩)
  | .E, 1, a :: M, (k + 3) :: W => some (.go ⟨.B, 0, 1 :: zs k ((a + 3) :: M), W⟩)
  | .F, 0, a :: M, [] => some (.pass M a)
  | .F, 0, a :: M, k :: W => some (.go ⟨.A, 0, (a + k + 1) :: M, W⟩)
  | .C, 0, (c + 1) :: M, 1 :: k :: W => some (.go ⟨.C, 0, 0 :: M, 1 :: (k + c + 1) :: W⟩)
  | .C, 0, (c + 1) :: M, k :: W => some (.go ⟨.B, 0, 1 :: zs k (c :: M), W⟩)
  | .C, 0, 0 :: d :: M, 1 :: W => some (.go ⟨.F, 0, 0 :: (d + 2) :: M, W⟩)
  | .C, 0, 0 :: d :: M, (k + 2) :: W => some (.go ⟨.B, 0, 1 :: zs k ((d + 2) :: M), W⟩)
  | .B, 0, 1 :: 0 :: y :: x :: M, [] => some (.pass ((x + 2) :: M) (y + 1))
  | .B, 0, n :: c :: d :: M, k :: W => bstep n c d M k W
  | _, _, _, _ => none

def astep (c : ACfg) : Option Out := astep' c.q c.h (pad 4 c.L) c.W

theorem bstep_sound {n c d k : Nat} {M W : List Nat} {o : Out} (e : bstep n c d M k W = some o) :
    Leads (enc ⟨.B, 0, n :: c :: d :: M, k :: W⟩) o := by
  unfold bstep at e
  split at e
  · cases e
    obtain ⟨j, rfl⟩ : ∃ j, n = 3 * j + 1 := ⟨n / 3, by omega⟩
    rw [show (3 * j + 1) / 3 = j by omega]; exact s_b_one c j k (d :: M) W
  split at e
  · cases e; subst n; exact s_b_two0 c k (d :: M) W
  split at e
  · cases e
    obtain ⟨j, rfl⟩ : ∃ j, n = 3 * j + 5 := ⟨n / 3 - 1, by omega⟩
    rw [show (3 * j + 5) / 3 - 1 = j by omega]; exact s_b_two c j k (d :: M) W
  split at e
  · cases e; subst k
    obtain ⟨j, rfl⟩ : ∃ j, n = 3 * j := ⟨n / 3, by omega⟩
    rw [show 3 * j / 3 = j by omega]; exact s_b_zero c j (d :: M) W
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  split at e
  · cases e; subst n; exact s_b_empty c k (d :: M) W
  split at e
  · cases e; subst n; exact s_b_three0 c d k M W
  · cases e
    obtain ⟨j, rfl⟩ : ∃ j, n = 3 * j + 6 := ⟨n / 3 - 2, by omega⟩
    rw [show (3 * j + 6) / 3 - 2 = j by omega]; exact s_b_three c d j k M W

theorem astep'_sound {q : St} {h : Nat} {L W : List Nat} {o : Out} (e : astep' q h L W = some o) :
    Leads (enc ⟨q, h, L, W⟩) o := by
  unfold astep' at e
  split at e <;> first | cases e | skip
  · exact s_a_run _ _ _ _
  · exact s_a_end _ _
  · exact s_a_tok _ _ _
  · exact s_d_halt _
  · exact s_d_one _ _ _
  · exact s_d_two _ _ _
  · exact s_d_tok _ _ _ _
  · exact s_e_halt _
  · exact s_e_one _ _ _
  · exact s_e_two _ _ _
  · exact s_e_tok _ _ _ _
  · exact s_f_end _ _
  · exact s_f_tok _ _ _ _
  · exact s_c_move _ _ _ _
  · exact s_c_tok _ _ _ _
  · exact s_c_one _ _ _
  · exact s_c_more _ _ _ _
  · exact s_b_end _ _ _
  · exact bstep_sound e

/-- **Every step of the block machine is sound** for the real machine (kernel only). -/
theorem astep_sound {c : ACfg} {o : Out} (e : astep c = some o) : Leads (enc c) o := by
  have h := astep'_sound e
  rwa [show enc ⟨c.q, c.h, pad 4 c.L, c.W⟩ = enc c by unfold enc; rw [lt_pad]] at h

/-- The block machine for at most `f` steps, until the pass is over. -/
def arun : Nat → ACfg → Option Out
  | 0, _ => none
  | f + 1, c =>
    match astep c with
    | some (.go c') => arun f c'
    | some o => some o
    | none => none

theorem arun_sound : ∀ (f : Nat) {c : ACfg} {o : Out}, arun f c = some o → Leads (enc c) o := by
  intro f
  induction f with
  | zero => intro c o e; cases e
  | succ f ih =>
    intro c o e
    unfold arun at e
    split at e
    · rename_i h; exact Leads.trans (astep_sound h) (ih e)
    · cases e; exact astep_sound (by assumption)
    · cases e

/-! ## The whole pass -/

/-- One pass from `K ls n` (the last block `n + 1`): `next` when the last block is not a multiple of 3, the block
machine for at most `f` steps when it is; `.pass ls' n'` for the next pass configuration `K ls' n'`, `.halt` if the
machine halts on the way. -/
def pass (f : Nat) (ls : List Nat) (n : Nat) : Option Out :=
  match next ls n with
  | some (ls', n') => some (.pass ls' n')
  | none =>
    if n = 0 then some .halt
    else if n % 3 = 2 then arun f ⟨.B, 0, pad 1 ls, 0 :: 1 :: tw 2 (n / 3) 0⟩
    else none

/-- **The pass map is sound**, for every last block, multiples of 3 included (kernel only). -/
theorem pass_sound {f : Nat} {ls : List Nat} {n : Nat} {o : Out} (e : pass f ls n = some o) : Leads (K ls n) o := by
  unfold pass at e
  split at e
  · rename_i h; cases e; exact next_sound h
  split at e
  · cases e; subst n
    obtain ⟨c, h₁, h₂⟩ := K_zero_halts ls
    exact ⟨6, c, h₁, h₂⟩
  split at e
  · obtain ⟨j, rfl⟩ : ∃ j, n = 3 * j + 2 := ⟨n / 3, by omega⟩
    rw [show (3 * j + 2) / 3 = j by omega] at e
    rw [K_pad1]
    exact Leads.trans (s_k_start _ j _) (arun_sound f e)
  · cases e

/-- The pass map iterated `p` times (each pass with at most `f` steps of the block machine). -/
def passes (f : Nat) : Nat → List Nat → Nat → Option Out
  | 0, ls, n => some (.pass ls n)
  | p + 1, ls, n =>
    match pass f ls n with
    | some (.pass ls' n') => passes f p ls' n'
    | o => o

theorem passes_sound (f : Nat) : ∀ (p : Nat) {ls : List Nat} {n : Nat} {o : Out},
    passes f p ls n = some o → Leads (K ls n) o := by
  intro p
  induction p with
  | zero => intro ls n o e; cases e; exact ⟨0, rfl⟩
  | succ p ih =>
    intro ls n o e
    unfold passes at e
    split at e
    · rename_i h; exact Leads.trans (pass_sound h) (ih e)
    · exact pass_sound e

/-- From blank tape: the first four pass starts (`blank_passes`), then 100 passes of `pass`, 32 of them recursive,
evaluated by the kernel: the pass start `1^162 0 1^206 A> 0^∞`, which the run reaches after 2065482 steps. -/
theorem blank_passes_104 : Reaches init (K [162] 205) := by
  have h := passes_sound 1000000 100 (ls := [10]) (n := 2) (o := .pass [162, 0, 0, 0] 205) (by decide +kernel)
  have e : K [162, 0, 0, 0] 205 = K [162] 205 := by simp only [K, lt, rep_zero, cons_false_blank]
  exact blank_passes.trans (e ▸ h)

end BB6c
