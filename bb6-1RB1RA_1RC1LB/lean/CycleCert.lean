import Periods

/-!
# The tables in pieces, for the kernel

`drive` (`Cascade.lean`) builds each level's table from the one before, but one kernel evaluation of it runs out of
memory past about 18 levels: the kernel keeps every intermediate term of a declaration.  Here the same computation is
cut into pieces that are separate declarations.  The tables are written out (by `cycle_gen.py`, as data in
`CycleData/`), and every piece is a short evaluation on a stretch of a written table:

* `lvSeg S p acc`: one pass of a level with block `p` over the stretch `S` of a table (no tail); a pass of the whole
  table is `lvPass` (`lvPass_seg`), and stretches chain (`lvSeg_app`);
* `pseg S U t`: the levels `U` over the stretch `S`; likewise for `pass` (`pass_pseg`, `pseg_app`);
* `Step`: one level of the plan, `r` passes of the table and the table for one more level; `step_sound` turns it
  into a point of the timed orbit and a table (`Rep`) of the bottom one level longer.

Nothing written is trusted: each piece is checked by `decide +kernel`, and the data only says what to check.
`rep_bs` turns a table into a cycle of the bottom, `bs P B = B`, with `P` its length (`build_len`: the new table is
`L` times as long).
-/

namespace BB6b

open TM

/-! ## A level over a stretch of a table -/

/-- One pass of the level with block `p` over the stretch `S`: the entries it passes on, in order, the super steps
and machine steps since its last event, and its block at the end. -/
def lvSeg : List Entry → Nat → Nat × Nat → List Entry × (Nat × Nat) × Nat
  | [], p, acc => ([], acc, p)
  | (dt, e, c) :: T, p, acc =>
    match lev p e with
    | (p', .none, c') => lvSeg T p' (acc.1 + dt, acc.2 + c + c')
    | (p', e', c') => match lvSeg T p' (0, 0) with
      | (o, a, q) => ((acc.1 + dt, e', acc.2 + c + c') :: o, a, q)

theorem lvPass_seg : ∀ (T : List Entry) (tl : Nat × Nat) (p : Nat) (acc : Nat × Nat) (out : List Entry),
    lvPass T tl p acc out = ((lvSeg T p acc).1.reverse ++ out, ((lvSeg T p acc).2.1.1 + tl.1,
      (lvSeg T p acc).2.1.2 + tl.2), (lvSeg T p acc).2.2) := by
  intro T
  induction T with
  | nil => intro tl p acc out; rfl
  | cons x T ih =>
    obtain ⟨dt, e, c⟩ := x
    intro tl p acc out
    simp only [lvPass, lvSeg]
    generalize lev p e = z
    obtain ⟨p', e', c'⟩ := z
    cases e' with
    | none => simp only; exact ih _ _ _ _
    | add a => simp only; rw [ih]; simp
    | wave h => simp only; rw [ih]; simp

theorem lvSeg_app : ∀ (A B : List Entry) (p : Nat) (acc : Nat × Nat) (o : List Entry) (a : Nat × Nat) (q : Nat)
    (o' : List Entry) (a' : Nat × Nat) (q' : Nat), lvSeg A p acc = (o, a, q) → lvSeg B q a = (o', a', q') →
    lvSeg (A ++ B) p acc = (o ++ o', a', q') := by
  intro A
  induction A with
  | nil => intro B p acc o a q o' a' q' h₁ h₂; cases h₁; exact h₂
  | cons x A ih =>
    obtain ⟨dt, e, c⟩ := x
    intro B p acc o a q o' a' q' h₁ h₂
    simp only [List.cons_append, lvSeg] at h₁ ⊢
    generalize lev p e = z at h₁ ⊢
    obtain ⟨p₁, e₁, c₁⟩ := z
    cases e₁ with
    | none => exact ih B _ _ o a q o' a' q' h₁ h₂
    | add v =>
      simp only at h₁ ⊢
      generalize hr : lvSeg A p₁ (0, 0) = r at h₁
      obtain ⟨o₁, a₁, q₁⟩ := r
      simp only [Prod.mk.injEq] at h₁
      obtain ⟨rfl, rfl, rfl⟩ := h₁
      rw [ih B _ _ o₁ _ _ o' a' q' hr h₂]; rfl
    | wave v =>
      simp only at h₁ ⊢
      generalize hr : lvSeg A p₁ (0, 0) = r at h₁
      obtain ⟨o₁, a₁, q₁⟩ := r
      simp only [Prod.mk.injEq] at h₁
      obtain ⟨rfl, rfl, rfl⟩ := h₁
      rw [ih B _ _ o₁ _ _ o' a' q' hr h₂]; rfl

/-- `L` passes of the level over the whole table, the tail added after each. -/
def lvSegs (T : List Entry) (tl : Nat × Nat) : Nat → Nat → Nat × Nat → List Entry × (Nat × Nat) × Nat
  | 0, p, acc => ([], acc, p)
  | L + 1, p, acc =>
    match lvSeg T p acc with
    | (o, a, q) => match lvSegs T tl L q (a.1 + tl.1, a.2 + tl.2) with
      | (o', a', q') => (o ++ o', a', q')

theorem buildAux_segs : ∀ (L : Nat) (T : List Entry) (tl : Nat × Nat) (p : Nat) (acc : Nat × Nat) (out : List Entry),
    buildAux L T tl p acc out = ((lvSegs T tl L p acc).1.reverse ++ out, (lvSegs T tl L p acc).2.1,
      (lvSegs T tl L p acc).2.2) := by
  intro L
  induction L with
  | zero => intro T tl p acc out; rfl
  | succ L ih =>
    intro T tl p acc out
    simp only [buildAux, lvSegs, lvPass_seg, ih]
    simp

theorem build_segs (T : List Entry) (tl : Nat × Nat) (p L : Nat) : build T tl p L = lvSegs T tl L p (0, 0) := by
  simp only [build, buildAux_segs]
  simp

theorem lvSegs_zero (T : List Entry) (tl : Nat × Nat) (p : Nat) (acc : Nat × Nat) :
    lvSegs T tl 0 p acc = ([], acc, p) := rfl

theorem lvSegs_succ (T : List Entry) (tl : Nat × Nat) (L p : Nat) (acc : Nat × Nat) (o : List Entry)
    (a : Nat × Nat) (q : Nat) (o' : List Entry) (acc' a' : Nat × Nat) (q' : Nat) (h₁ : lvSeg T p acc = (o, a, q))
    (h₂ : lvSegs T tl L q acc' = (o', a', q')) (ha : acc' = (a.1 + tl.1, a.2 + tl.2)) :
    lvSegs T tl (L + 1) p acc = (o ++ o', a', q') := by
  subst ha; simp only [lvSegs, h₁, h₂]

/-! ## The levels further left over a stretch -/

/-- The levels `U` over the stretch `S` of a table (no tail). -/
def pseg : List Entry → List Nat → Nat → Option (List Nat × Nat)
  | [], U, t => some (U, t)
  | (_, e, c) :: T, U, t =>
    match push e U with
    | none => none
    | some U' => pseg T U' (t + c + pushT e U)

theorem pass_pseg : ∀ (T : List Entry) (tl : Nat × Nat) (U : List Nat) (t : Nat),
    pass T tl U t = (pseg T U t).map (fun x => (x.1, x.2 + tl.2)) := by
  intro T
  induction T with
  | nil => intro tl U t; rfl
  | cons x T ih =>
    obtain ⟨dt, e, c⟩ := x
    intro tl U t
    simp only [pass, pseg]
    cases push e U with
    | none => rfl
    | some U' => exact ih _ _ _

theorem pseg_app : ∀ (A B : List Entry) (U U' U'' : List Nat) (t t' t'' : Nat), pseg A U t = some (U', t') →
    pseg B U' t' = some (U'', t'') → pseg (A ++ B) U t = some (U'', t'') := by
  intro A
  induction A with
  | nil => intro B U U' U'' t t' t'' h₁ h₂; cases h₁; exact h₂
  | cons x A ih =>
    obtain ⟨dt, e, c⟩ := x
    intro B U U' U'' t t' t'' h₁ h₂
    simp only [List.cons_append, pseg] at h₁ ⊢
    cases e' : push e U with
    | none => rw [e'] at h₁; cases h₁
    | some V => rw [e'] at h₁; exact ih B V U' U'' _ t' t'' h₁ h₂

theorem pass_of_pseg (T : List Entry) (tl : Nat × Nat) (U U' : List Nat) (t t' : Nat) (h : pseg T U t = some (U', t')) :
    pass T tl U t = some (U', t' + tl.2) := by
  rw [pass_pseg, h]; rfl

theorem passes_zero (T : List Entry) (tl : Nat × Nat) (U : List Nat) (t : Nat) : passes 0 T tl U t = some (U, t) := rfl

theorem passes_succ (r : Nat) (T : List Entry) (tl : Nat × Nat) (U U' : List Nat) (t t' : Nat) (x : List Nat × Nat)
    (h₁ : pass T tl U t = some (U', t')) (h₂ : passes r T tl U' t' = some x) : passes (r + 1) T tl U t = some x := by
  simp only [passes, h₁, h₂]

/-! ## One level of the plan -/

/-- A level of the plan, checked: from the bottom `B` with table `T` (tail `tl`) and the levels `U` at machine step
`t`, `r` passes take `U` to `p :: U'` at step `t'`, and the table for one more level, over `L` passes of `p`, is
`T'` with tail `tl'`, bringing `p` back. -/
theorem step_sound (B : List Nat) (T : List Entry) (tl : Nat × Nat) (U : List Nat) (t : Nat) (r L p : Nat)
    (U' : List Nat) (t' : Nat) (T' : List Entry) (tl' : Nat × Nat) (hR : Rep B T tl) (hU : U ≠ [])
    (hp : passes r T tl U t = some (p :: U', t')) (hb : build T tl p L = (T', tl', p)) :
    (∃ j, orbitT j (B ++ U) t = some ((B ++ [p]) ++ U', t')) ∧ Rep (B ++ [p]) T' tl' := by
  obtain ⟨j, hj⟩ := passes_sound r T tl B U _ t t' hU hR hp
  refine ⟨⟨j, by simpa using hj⟩, ?_⟩
  have := build_rep B T tl p L hR (by rw [hb])
  rw [hb] at this
  exact this

/-! ## A table is a cycle -/

theorem quiet_bs : ∀ (n : Nat) (B : List Nat) (c : Nat) (B' : List Nat), Quiet n B c B' → bs n B = B' := by
  intro n
  induction n with
  | zero => intro B c B' h; exact h.2.symm
  | succ n ih => intro B c B' h; obtain ⟨_, c', _, h⟩ := h; exact ih _ _ _ h

theorem chain_bs : ∀ (T : List Entry) (B B' : List Nat), Chain B T B' → bs (lenT T) B = B' := by
  intro T
  induction T with
  | nil => intro B B' h; cases h; rfl
  | cons x T ih =>
    obtain ⟨dt, e, c⟩ := x
    intro B B' h
    obtain ⟨n, c₁, Bm, rfl, hq, _, _, hc⟩ := h
    have h₁ := quiet_bs n B c₁ Bm hq
    rw [show lenT ((n + 1, e, c) :: T) = n + 1 + lenT T by simp [lenT], bs_add, bs_add, h₁]
    exact ih _ _ hc

/-- **A table is a cycle**: the bottom comes back after the table's length in super steps. -/
theorem rep_bs (B : List Nat) (T : List Entry) (tl : Nat × Nat) (h : Rep B T tl) : bs (lenT T + tl.1) B = B := by
  obtain ⟨B', hc, hq⟩ := h
  rw [bs_add, chain_bs T B B' hc]
  exact quiet_bs _ _ _ _ hq

theorem lvSeg_len : ∀ (S : List Entry) (p : Nat) (acc : Nat × Nat),
    lenT (lvSeg S p acc).1 + (lvSeg S p acc).2.1.1 = acc.1 + lenT S := by
  intro S
  induction S with
  | nil => intro p acc; simp [lvSeg, lenT]
  | cons x S ih =>
    obtain ⟨dt, e, c⟩ := x
    intro p acc
    simp only [lvSeg]
    generalize lev p e = z
    obtain ⟨p', e', c'⟩ := z
    have h₁ := ih p' (0, 0)
    have h₂ := ih p' (acc.1 + dt, acc.2 + c + c')
    cases e' with
    | none => simp only at h₂ ⊢; rw [h₂]; simp [lenT]; omega
    | add a =>
      simp only
      generalize lvSeg S p' (0, 0) = r at h₁ ⊢
      obtain ⟨o, a, q⟩ := r
      simp only [lenT, List.map_cons, List.sum_cons] at h₁ ⊢
      omega
    | wave h =>
      simp only
      generalize lvSeg S p' (0, 0) = r at h₁ ⊢
      obtain ⟨o, a, q⟩ := r
      simp only [lenT, List.map_cons, List.sum_cons] at h₁ ⊢
      omega

theorem lvSegs_len : ∀ (L : Nat) (T : List Entry) (tl : Nat × Nat) (p : Nat) (acc : Nat × Nat),
    lenT (lvSegs T tl L p acc).1 + (lvSegs T tl L p acc).2.1.1 = acc.1 + L * (lenT T + tl.1) := by
  intro L
  induction L with
  | zero => intro T tl p acc; simp [lvSegs, lenT]
  | succ L ih =>
    intro T tl p acc
    have h₁ := lvSeg_len T p acc
    simp only [lvSegs]
    generalize lvSeg T p acc = r at h₁
    obtain ⟨o, a, q⟩ := r
    have h₂ := ih T tl q (a.1 + tl.1, a.2 + tl.2)
    generalize lvSegs T tl L q (a.1 + tl.1, a.2 + tl.2) = s at h₂
    obtain ⟨o', a', q'⟩ := s
    simp only [lenT, List.map_append, List.sum_append] at h₁ h₂ ⊢
    rw [Nat.succ_mul]
    omega

/-- **The table for one more level is `L` times as long.** -/
theorem build_len (T : List Entry) (tl : Nat × Nat) (p L : Nat) :
    lenT (build T tl p L).1 + (build T tl p L).2.1.1 = L * (lenT T + tl.1) := by
  rw [build_segs]; have := lvSegs_len L T tl p (0, 0); simp only at this; omega

/-- `build_len` in the form the generated files use (no evaluation of `lenT` on a written table). -/
theorem build_len' {T T' : List Entry} {tl tl' : Nat × Nat} {p p' L P : Nat} (hb : build T tl p L = (T', tl', p'))
    (hP : lenT T + tl.1 = P) : lenT T' + tl'.1 = L * P := by
  have h := build_len T tl p L
  rw [hb, hP] at h
  exact h

/-! ## Least periods

The table of one more level is built over `L` passes of its block `p`, and the block comes back after `L` passes and
not before (the generated files check this).  Then `L` times the least period of the bottom is the least period of
the bottom with one more level. -/

/-- `m` is the least period of the bottom `B`: it comes back after `m` super steps, and only after multiples of `m`. -/
def LeastP (B : List Nat) (m : Nat) : Prop := 0 < m ∧ bs m B = B ∧ ∀ n, bs n B = B → m ∣ n

theorem least₀ : LeastP [] 1 := by
  refine ⟨by decide, rfl, fun n _ => Nat.one_dvd n⟩

/-- `F` takes `q` to the first of `l`, each of `l` to the next, and the last to `e`. -/
def Steps (F : Nat → Nat) : Nat → List Nat → Nat → Prop
  | q, [], e => F q = e
  | q, b :: l, e => F q = b ∧ Steps F b l e

theorem iter_steps (F : Nat → Nat) : ∀ (l : List Nat) (q e : Nat), Steps F q l e →
    iter F (l.length + 1) q = e ∧ ∀ i, i < l.length → iter F (i + 1) q = l.getD i 0 := by
  intro l
  induction l with
  | nil => intro q e h; exact ⟨h, fun i hi => absurd hi (by simp)⟩
  | cons b l ih =>
    intro q e h
    obtain ⟨h₁, h₂⟩ := h
    obtain ⟨ih₁, ih₂⟩ := ih b e h₂
    refine ⟨by simp only [List.length_cons, iter, h₁]; exact ih₁, ?_⟩
    intro i hi
    cases i with
    | zero => simp [iter, h₁]
    | succ i =>
      simp only [List.length_cons] at hi
      simp only [iter, h₁, List.getD_cons_succ]
      exact ih₂ i (by omega)

/-- **The least period of one more level**: if the next level's block `p`, read once per period `m` of the bottom
`B`, runs through `l` and comes back, never meeting `p` in between, the least period of `B ++ [p]` is
`(l.length + 1) * m`. -/
theorem least_append (B : List Nat) (m p : Nat) (l : List Nat) (h : LeastP B m) (hs : Steps (topv m B) p l p)
    (hn : p ∉ l) : LeastP (B ++ [p]) ((l.length + 1) * m) := by
  obtain ⟨hm, hB, hd⟩ := h
  obtain ⟨hL, hi⟩ := iter_steps _ l p p hs
  refine ⟨Nat.mul_pos (by omega) hm, by rw [bs_iter B m hB, hL], ?_⟩
  intro n hn'
  rw [bs_append] at hn'
  obtain ⟨h₁, h₂⟩ := List.append_inj' hn' rfl
  simp only [List.cons.injEq, and_true] at h₂
  obtain ⟨r, rfl⟩ := hd n h₁
  have hr : iter (topv m B) r p = p := by
    have := bs_iter B m hB r p
    rw [Nat.mul_comm] at this
    rw [bs_append, h₁, h₂] at this
    exact (List.cons.inj (List.append_cancel_left this)).1.symm
  obtain ⟨a, b, hb, rfl⟩ : ∃ a b, b < l.length + 1 ∧ r = b + a * (l.length + 1) :=
    ⟨r / (l.length + 1), r % (l.length + 1), Nat.mod_lt _ (by omega), by
      have := Nat.div_add_mod r (l.length + 1); rw [Nat.mul_comm] at this; omega⟩
  rw [iter_add, iter_mul _ _ _ hL] at hr
  cases b with
  | zero => exact ⟨a, by rw [Nat.mul_comm (l.length + 1), Nat.mul_assoc]; simp [Nat.mul_comm]⟩
  | succ b =>
    exfalso
    rw [(hi b (by omega))] at hr
    have hb' : b < l.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb'] at hr
    exact hn (hr ▸ List.getElem_mem hb')

theorem lvSeg_blk : ∀ (T : List Entry) (q : Nat) (acc acc' : Nat × Nat), (lvSeg T q acc).2.2 = (lvSeg T q acc').2.2 := by
  intro T
  induction T with
  | nil => intro q acc acc'; rfl
  | cons x T ih =>
    obtain ⟨dt, e, c⟩ := x
    intro q acc acc'
    simp only [lvSeg]
    generalize lev q e = z
    obtain ⟨p', e', c'⟩ := z
    cases e' with
    | none => exact ih _ _ _
    | add a => rfl
    | wave h => rfl

/-- **A pass over the table is the pass map**: the block at the end of a pass over the table of `B` is the pass map
`topv m B` of the block at its start. -/
theorem topv_of_seg {B : List Nat} {T : List Entry} {tl : Nat × Nat} {m q q' : Nat} {acc a : Nat × Nat}
    {o : List Entry} (hR : Rep B T tl) (hm : lenT T + tl.1 = m) (h : lvSeg T q acc = (o, a, q')) :
    topv m B q = q' := by
  obtain ⟨Bend, hc, hq⟩ := hR
  obtain ⟨S', h₁, h₂⟩ := lvPass_chain T tl B Bend B (B ++ [q]) (B ++ [q]) q (0, 0) [] hc hq rfl ⟨rfl, rfl⟩
  have e₁ := chain_bs _ _ _ h₁
  have e₂ := quiet_bs _ _ _ _ h₂
  have hl := lvSeg_len T q (0, 0)
  have hb : (lvSeg T q (0, 0)).2.2 = q' := by rw [lvSeg_blk T q (0, 0) acc, h]
  rw [lvPass_seg] at e₁ e₂
  simp only [List.append_nil, List.reverse_reverse] at e₁ e₂
  have e := bs_add (lenT (lvSeg T q (0, 0)).1) ((lvSeg T q (0, 0)).2.1.1 + tl.1) (B ++ [q])
  rw [e₁, e₂, hb, show lenT (lvSeg T q (0, 0)).1 + ((lvSeg T q (0, 0)).2.1.1 + tl.1) = m by omega,
    bs_append] at e
  exact (List.cons.inj (List.append_inj' e rfl).2).1

/-- The timed orbit is the orbit. -/
theorem orbitT_orbit : ∀ (j : Nat) (L : List Nat) (t : Nat) (W : List Nat) (t' : Nat),
    orbitT j L t = some (W, t') → orbit j L = some W := by
  intro j
  induction j with
  | zero => intro L t W t' h; cases h; rfl
  | succ j ih =>
    intro L t W t' h
    simp only [orbitT] at h
    cases e : superL L with
    | none => rw [e] at h; cases h
    | some L' => rw [e] at h; simp only [orbit, e, Option.bind_some]; exact ih _ _ _ _ h

end BB6b
