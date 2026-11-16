import Exec

/-!
# Classes of node tapes, split trees, and "halts if and only if"

A *node* is the tape at an event: state F at the left end of the tape, the right side a *text* (cells and blocks,
`Seg`) with a count for each block.  A *class* is a text with a residue `r` mod `MOD` for every count: its members
are the nodes with counts `≥ BIG` and `≡ r` mod `MOD` (`ValidV`).  The counts of a class are `rootC`, the forms
`base r + MOD xᵢ` with free variables `xᵢ`.

A class carries a *split tree* (`STree`): an inner node is a primitive split of the variables (`Split`: a residue of
one variable, the first values of one variable, or the comparison of two variables), whose children together cover
every value (`kids_cover`); a leaf is either one run of the executor to a node of a class of the list (`Leaf.node`),
or one run to a halting configuration (`Leaf.halt`).  `chk` checks the tree (every split well formed, every leaf by
the given test); `chk_sound` turns it into a statement for every value of the variables.

`halts_iff_of_checks`: with every class checked, every entry of the list `pre` checked, and an arrival from blank tape
in a class that does not halt, the machine halts from blank tape if and only if its run reaches a tape of `pre`.  The
classes marked `isH` are the halting ones (all their leaves halt); a leaf of any other class runs to a node of a class
that is not marked, unless its own start is an entry of `pre` (and then the entry is checked to run into a marked
class).
-/

namespace H163738M

open TM

/-! ## Substitutions -/

def upd (ρ : Nat → Nat) (v e : Nat) : Nat → Nat := fun i => if i = v then e else ρ i

/-- The coefficient list of `d xᵥ`. -/
def unitL (v d : Nat) : List Nat := List.replicate v 0 ++ [d]

def zeroAt : Nat → List Nat → List Nat
  | _, [] => []
  | 0, _ :: as => 0 :: as
  | v + 1, a :: as => a :: zeroAt v as

def getAt : Nat → List Nat → Nat
  | _, [] => 0
  | 0, a :: _ => a
  | v + 1, _ :: as => getAt v as

theorem dot_upd (a : List Nat) (v e : Nat) (ρ : Nat → Nat) :
    dot a (upd ρ v e) = dot (zeroAt v a) ρ + getAt v a * e := by
  induction a generalizing v ρ with
  | nil => simp [dot, zeroAt, getAt]
  | cons x as ih =>
    cases v with
    | zero =>
      have hf : (fun i => upd ρ 0 e (i + 1)) = (fun i => ρ (i + 1)) := by
        funext i; simp [upd]
      simp only [dot, zeroAt, getAt, hf]
      simp [upd]
      omega
    | succ v =>
      have hf : (fun i => upd ρ (v + 1) e (i + 1)) = upd (fun i => ρ (i + 1)) v e := by
        funext i; simp [upd]
      simp only [dot, zeroAt, getAt, hf, ih]
      simp [upd]
      omega

theorem upd_self (ρ : Nat → Nat) (v : Nat) : upd ρ v (ρ v) = ρ := by
  funext i; simp only [upd]; split <;> simp_all

theorem dot_zeroAt (a : List Nat) (v : Nat) (ρ : Nat → Nat) (h : getAt v a = 0) :
    dot (zeroAt v a) ρ = dot a ρ := by
  have := dot_upd a v (ρ v) ρ
  rw [upd_self, h] at this
  omega

/-- `n` with `xᵥ := k + m·x`. -/
def Cnt.subst (n : Cnt) (v k : Nat) (m : List Nat) : Cnt :=
  if getAt v n.a = 0 then n
  else ⟨n.c + getAt v n.a * k, trimL (addL (zeroAt v n.a) (m.map (getAt v n.a * ·)))⟩

theorem Cnt.eval_subst (ρ : Nat → Nat) (n : Cnt) (v k : Nat) (m : List Nat) :
    (n.subst v k m).eval ρ = n.eval (upd ρ v ((⟨k, m⟩ : Cnt).eval ρ)) := by
  unfold Cnt.subst
  split
  · rename_i h
    simp only [Cnt.eval, dot_upd, h, dot_zeroAt _ _ _ h]
    omega
  · simp only [Cnt.eval, dot_trimL, dot_addL, dot_map_mul, dot_upd, Nat.mul_add]
    omega

def evals (ρ : Nat → Nat) (cs : List Cnt) : List Nat := cs.map (Cnt.eval ρ)

def substAll (cs : List Cnt) (v k : Nat) (m : List Nat) : List Cnt := cs.map (fun n => n.subst v k m)

theorem evals_substAll (ρ : Nat → Nat) (cs : List Cnt) (v k : Nat) (m : List Nat) :
    evals ρ (substAll cs v k m) = evals (upd ρ v ((⟨k, m⟩ : Cnt).eval ρ)) cs := by
  simp only [evals, substAll, List.map_map]
  congr 1
  funext n
  simp [Cnt.eval_subst]

theorem eval_unit (ρ : Nat → Nat) (k v d : Nat) : (⟨k, unitL v d⟩ : Cnt).eval ρ = k + d * ρ v := by
  simp [Cnt.eval, unitL, dot_replicate]

theorem eval_pair (ρ : Nat → Nat) (k u w : Nat) :
    (⟨k, addL (unitL u 1) (unitL w 1)⟩ : Cnt).eval ρ = k + ρ u + ρ w := by
  simp only [Cnt.eval, dot_addL, unitL, dot_replicate]
  omega

/-! ## Primitive splits -/

inductive Split where
  /-- `xᵥ := j + d xᵥ` for `j < d`. -/
  | res (v d : Nat)
  /-- `xᵥ := j` for `j < t`, and `xᵥ := t + xᵥ`. -/
  | peel (v t : Nat)
  /-- `xᵤ := xᵤ + x_w` (`xᵤ ≥ x_w`), and `x_w := 1 + xᵤ + x_w` (`x_w > xᵤ`). -/
  | cmp (u w : Nat)
  deriving DecidableEq, Repr

def Split.ok : Split → Bool
  | .res _ d => 0 < d
  | .peel _ _ => true
  | .cmp u w => u != w

/-- The counts of the children. -/
def kids (cs : List Cnt) : Split → List (List Cnt)
  | .res v d => (List.range d).map (fun j => substAll cs v j (unitL v d))
  | .peel v t => (List.range t).map (fun j => substAll cs v j []) ++ [substAll cs v t (unitL v 1)]
  | .cmp u w => [substAll cs u 0 (addL (unitL u 1) (unitL w 1)), substAll cs w 1 (addL (unitL u 1) (unitL w 1))]

/-- The children of a split cover every value of the variables. -/
theorem kids_cover (cs : List Cnt) (s : Split) (hs : s.ok = true) (ρ : Nat → Nat) :
    ∃ cs' ∈ kids cs s, ∃ ρ', evals ρ' cs' = evals ρ cs := by
  cases s with
  | res v d =>
    simp only [Split.ok, decide_eq_true_eq] at hs
    refine ⟨substAll cs v (ρ v % d) (unitL v d), ?_, upd ρ v (ρ v / d), ?_⟩
    · simp only [kids, List.mem_map, List.mem_range]
      exact ⟨ρ v % d, Nat.mod_lt _ hs, rfl⟩
    · rw [evals_substAll, eval_unit]
      have : upd (upd ρ v (ρ v / d)) v (ρ v % d + d * upd ρ v (ρ v / d) v) = ρ := by
        funext i
        simp only [upd]
        split
        · rename_i h; subst h; simp [Nat.mod_add_div]
        · rfl
      rw [this]
  | peel v t =>
    by_cases h : ρ v < t
    · refine ⟨substAll cs v (ρ v) [], ?_, ρ, ?_⟩
      · simp only [kids, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inl ⟨ρ v, h, rfl⟩
      · rw [evals_substAll]
        simp [Cnt.eval, dot, upd_self]
    · refine ⟨substAll cs v t (unitL v 1), ?_, upd ρ v (ρ v - t), ?_⟩
      · simp [kids]
      · rw [evals_substAll, eval_unit]
        have : upd (upd ρ v (ρ v - t)) v (t + 1 * upd ρ v (ρ v - t) v) = ρ := by
          funext i
          simp only [upd]
          split
          · rename_i e; subst e; simp; omega
          · rfl
        rw [this]
  | cmp u w =>
    simp only [Split.ok, bne_iff_ne, ne_eq] at hs
    by_cases h : ρ w ≤ ρ u
    · refine ⟨substAll cs u 0 (addL (unitL u 1) (unitL w 1)), by simp [kids], upd ρ u (ρ u - ρ w), ?_⟩
      rw [evals_substAll, eval_pair]
      have : upd (upd ρ u (ρ u - ρ w)) u (0 + upd ρ u (ρ u - ρ w) u + upd ρ u (ρ u - ρ w) w) = ρ := by
        funext i
        have hw : (w = u) = False := by simp; exact fun e => hs e.symm
        simp only [upd, hw, ite_false, ite_true]
        split
        · rename_i e; subst e; omega
        · rfl
      rw [this]
    · refine ⟨substAll cs w 1 (addL (unitL u 1) (unitL w 1)), by simp [kids], upd ρ w (ρ w - ρ u - 1), ?_⟩
      rw [evals_substAll, eval_pair]
      have : upd (upd ρ w (ρ w - ρ u - 1)) w (1 + upd ρ w (ρ w - ρ u - 1) u + upd ρ w (ρ w - ρ u - 1) w) = ρ := by
        funext i
        have hu : (u = w) = False := by simp; exact hs
        simp only [upd, hu, ite_false, ite_true]
        split
        · rename_i e; subst e; omega
        · rfl
      rw [this]

/-! ## Split trees -/

inductive STree (L : Type) where
  | leaf (l : L)
  | node (s : Split) (ch : List (STree L))

section
variable {L : Type} (f : List Cnt → L → Bool)

mutual
def chk (cs : List Cnt) : STree L → Bool
  | .leaf l => f cs l
  | .node s ch => s.ok && chkL (kids cs s) ch

def chkL : List (List Cnt) → List (STree L) → Bool
  | [], [] => true
  | c :: css, t :: ts => chk c t && chkL css ts
  | _, _ => false
end

variable {f} (G : List Nat → Prop) (hf : ∀ cs l, f cs l = true → ∀ ρ, G (evals ρ cs))
include hf

mutual
theorem chk_sound : (t : STree L) → (cs : List Cnt) → chk f cs t = true → ∀ ρ, G (evals ρ cs)
  | .leaf l, cs, h => hf cs l h
  | .node s ch, cs, h => by
    simp only [chk, Bool.and_eq_true] at h
    intro ρ
    obtain ⟨cs', hm, ρ', he⟩ := kids_cover cs s h.1 ρ
    rw [← he]
    exact chkL_sound ch (kids cs s) h.2 cs' hm ρ'

theorem chkL_sound : (ts : List (STree L)) → (css : List (List Cnt)) → chkL f css ts = true →
    ∀ cs ∈ css, ∀ ρ, G (evals ρ cs)
  | [], [], _ => by intro cs hm; cases hm
  | t :: ts, c :: css, h => by
    simp only [chkL, Bool.and_eq_true] at h
    intro cs hm ρ
    rcases List.mem_cons.1 hm with e | hm'
    · subst e; exact chk_sound t cs h.1 ρ
    · exact chkL_sound ts css h.2 cs hm' ρ
  | [], _ :: _, h => by simp [chkL] at h
  | _ :: _, [], h => by simp [chkL] at h
end
end

/-! ## Texts and node tapes -/

inductive Seg where
  | cells (w : List Bool)
  | blk (w : List Bool)
  deriving DecidableEq, Repr

/-- The tokens of a text with the given counts (nearest cell first). -/
def build : List Seg → List Cnt → List Tok
  | [], _ => []
  | .cells w :: s, cs => w.map .cell ++ build s cs
  | .blk w :: s, c :: cs => .blk w c :: build s cs
  | .blk w :: s, [] => .blk w ⟨0, []⟩ :: build s []

def consts (vs : List Nat) : List Cnt := vs.map (fun v => ⟨v, []⟩)

/-- The node with text `t` and counts `vs`: state F at the left end of the tape. -/
def nodeCfg (t : List Seg) (vs : List Nat) : Config := ⟨blank, dn (fun _ => 0) (build t (consts vs)), .F⟩

theorem dn_build (ρ : Nat → Nat) (t : List Seg) (cs : List Cnt) :
    dn ρ (build t cs) = dn (fun _ => 0) (build t (consts (evals ρ cs))) := by
  induction t generalizing cs with
  | nil => rfl
  | cons s t ih =>
    cases s with
    | cells w => simp only [build, dn_cells, ih]
    | blk w =>
      cases cs with
      | nil => simp only [build, dn, ih]; rfl
      | cons c cs => simp only [build, consts, evals, List.map_cons, dn, ih]; simp [Cnt.eval, dot]

/-- The executor's configuration of a node. -/
def startS (t : List Seg) (cs : List Cnt) : SCfg := ⟨[], build t cs, .F⟩

theorem den_startS (ρ : Nat → Nat) (t : List Seg) (cs : List Cnt) :
    den ρ (startS t cs) = nodeCfg t (evals ρ cs) := by
  show (⟨dn ρ [], dn ρ (build t cs), .F⟩ : Config) = _
  rw [dn_build]
  rfl

/-! ## Classes -/

def BIG : Nat := 20
def MOD : Nat := 2

/-- Counts of a member of a class with residues `res`. -/
def ValidV : List Nat → List Nat → Prop
  | [], [] => True
  | v :: vs, r :: rs => BIG ≤ v ∧ v % MOD = r % MOD ∧ ValidV vs rs
  | _, _ => False

def validB : List Cnt → List Nat → Bool
  | [], [] => true
  | n :: ns, r :: rs => BIG ≤ n.c && n.a.all (· % MOD == 0) && n.c % MOD == r % MOD && validB ns rs
  | _, _ => false

theorem dvd_dot (M : Nat) (as : List Nat) (ρ : Nat → Nat) (h : as.all (· % M == 0) = true) : M ∣ dot as ρ := by
  induction as generalizing ρ with
  | nil => exact Nat.dvd_zero _
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    exact Nat.dvd_add (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero h.1) (Nat.dvd_mul_right _ _)) (ih _ h.2)

theorem validB_sound {cs : List Cnt} {res : List Nat} (h : validB cs res = true) (ρ : Nat → Nat) :
    ValidV (evals ρ cs) res := by
  induction cs generalizing res with
  | nil => cases res <;> simp_all [validB, ValidV, evals]
  | cons n ns ih =>
    cases res with
    | nil => simp [validB] at h
    | cons r rs =>
      simp only [validB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
      obtain ⟨q, hq⟩ := dvd_dot MOD n.a ρ h2
      have e : n.eval ρ = n.c + MOD * q := by simp [Cnt.eval, hq]
      refine ⟨?_, ?_, ih h4⟩
      · simp only [e]; omega
      · simp only [e, Nat.add_mul_mod_self_left]; exact h3

def base (r : Nat) : Nat := BIG + (r + MOD - BIG % MOD) % MOD

/-- The counts of a class: `base rᵢ + MOD xᵢ`, the variable of the `i`-th count being `xᵢ`. -/
def rootC : Nat → List Nat → List Cnt
  | _, [] => []
  | i, r :: rs => ⟨base r, unitL i MOD⟩ :: rootC (i + 1) rs

theorem rootC_upd (ρ : Nat → Nat) (k x : Nat) : ∀ (i : Nat) (rs : List Nat), k < i →
    evals (upd ρ k x) (rootC i rs) = evals ρ (rootC i rs)
  | _, [], _ => rfl
  | i, r :: rs, h => by
    have ih := rootC_upd ρ k x (i + 1) rs (by omega)
    simp only [rootC, evals, List.map_cons] at ih ⊢
    rw [ih]
    simp only [eval_unit, upd]
    have : (i = k) = False := by simp; omega
    simp [this]

theorem rootC_onto : ∀ (i : Nat) (vs rs : List Nat), ValidV vs rs → ∃ ρ, evals ρ (rootC i rs) = vs
  | _, [], [], _ => ⟨fun _ => 0, rfl⟩
  | i, v :: vs, r :: rs, h => by
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨ρ, hρ⟩ := rootC_onto (i + 1) vs rs h3
    refine ⟨upd ρ i ((v - base r) / MOD), ?_⟩
    simp only [rootC, evals, List.map_cons] at hρ ⊢
    have := rootC_upd ρ i ((v - base r) / MOD) (i + 1) rs (by omega)
    simp only [evals] at this
    rw [this, hρ, eval_unit]
    simp only [upd, ite_true, base, BIG, MOD] at h1 h2 ⊢
    congr 1
    omega
  | _, [], _ :: _, h => by simp [ValidV] at h
  | _, _ :: _, [], h => by simp [ValidV] at h

/-! ## Leaves, classes, and the checks -/

/-- A leaf: `halt K` (K moves of the executor end at a halting configuration), or `node K j cs` (K + 1 moves, the
first a machine step, end at the node of class `j` with counts `cs`). -/
inductive Leaf where
  | halt (K : Nat)
  | node (K j : Nat) (cs : List Cnt)

structure Cls where
  text : List Seg
  res : List Nat
  /-- The halting class: all its leaves halt. -/
  isH : Bool
  tree : STree Leaf

/-- A start that runs into a halting class: K + 1 moves from the node `text`, `cs` end at the node of class `j`
with counts `tcs`. -/
structure PreE where
  text : List Seg
  cs : List Cnt
  K : Nat
  j : Nat
  tcs : List Cnt

/-- The configuration `S` is the node of class `d` with counts `cs` (both brought to the normal form `canon`). -/
def atNode (S : SCfg) (d : Cls) (cs : List Cnt) : Bool :=
  S.l == [] && S.st == .F && canon S.r == canon (build d.text cs) && validB cs d.res

theorem atNode_sound {S : SCfg} {d : Cls} {cs : List Cnt} (h : atNode S d cs = true) (ρ : Nat → Nat) :
    den ρ S = nodeCfg d.text (evals ρ cs) ∧ ValidV (evals ρ cs) d.res := by
  obtain ⟨l, r, st⟩ := S
  simp only [atNode, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hl, hs⟩, hc⟩, hv⟩ := h
  subst hl hs
  refine ⟨?_, validB_sound hv ρ⟩
  rw [← den_startS]
  show (⟨dn ρ [], dn ρ r, .F⟩ : Config) = ⟨dn ρ [], dn ρ (build d.text cs), .F⟩
  rw [← canon_spec ρ r, hc, canon_spec]

/-- The executor's run from `S`: K + 1 moves, the first one a machine step, ending at the node of class `d`. -/
def runTo (T : Tbl) (S : SCfg) (K : Nat) (d : Cls) (cs : List Cnt) : Bool :=
  cross T.shR T.shL S == none &&
    match run T (K + 1) S with
    | some S' => atNode S' d cs
    | none => false

theorem runTo_sound {T : Tbl} (hT : T.OK) {S : SCfg} {K : Nat} {d : Cls} {cs : List Cnt}
    (h : runTo T S K d cs = true) (ρ : Nat → Nat) :
    ∃ n, 0 < n ∧ steps n (den ρ S) = some (nodeCfg d.text (evals ρ cs)) ∧ ValidV (evals ρ cs) d.res := by
  simp only [runTo, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hc, h⟩ := h
  split at h
  · rename_i S' hr
    obtain ⟨n, hn, hs⟩ := run_pos hT K hc hr ρ
    obtain ⟨e, hv⟩ := atNode_sound h ρ
    exact ⟨n, hn, e ▸ hs, hv⟩
  · cases h

section
variable (cl : List Cls) (pre : List PreE) (T : Tbl)

def leafOK (c : Cls) (cs : List Cnt) : Leaf → Bool
  | .halt K => c.isH &&
    match run T K (startS c.text cs) with
    | some S' => haltS S'
    | none => false
  | .node K j tcs => !c.isH &&
    match cl[j]? with
    | some d => runTo T (startS c.text cs) K d tcs && (!d.isH || pre.any (fun p => p.text == c.text && p.cs == cs))
    | none => false

def preOK (p : PreE) : Bool :=
  match cl[p.j]? with
  | some d => d.isH && runTo T (startS p.text p.cs) p.K d p.tcs
  | none => false

def clsOK (c : Cls) : Bool := chk (leafOK cl pre T c) (rootC 0 c.res) c.tree

/-- What a node of class `c` with counts `vs` does: it halts (halting class), or it reaches a node of a class of the
list in at least one step, and a halting class only from a start listed in `pre`. -/
def Good (c : Cls) (vs : List Nat) : Prop :=
  if c.isH then Halts trans (nodeCfg c.text vs)
  else ∃ n, 0 < n ∧ ∃ d ∈ cl, ∃ vs', ValidV vs' d.res ∧ steps n (nodeCfg c.text vs) = some (nodeCfg d.text vs') ∧
    (d.isH = true → ∃ p ∈ pre, ∃ ρ, nodeCfg c.text vs = nodeCfg p.text (evals ρ p.cs))

end

theorem leafOK_sound {cl : List Cls} {pre : List PreE} {T : Tbl} (hT : T.OK) (c : Cls) :
    ∀ cs l, leafOK cl pre T c cs l = true → ∀ ρ, Good cl pre c (evals ρ cs) := by
  intro cs l h ρ
  cases l with
  | halt K =>
    simp only [leafOK, Bool.and_eq_true] at h
    obtain ⟨hH, h⟩ := h
    simp only [Good, hH, ite_true]
    split at h
    · rename_i S' hr
      obtain ⟨n, hn⟩ := run_sound hT K hr ρ
      rw [den_startS] at hn
      exact ⟨n, _, hn, haltS_sound ρ h⟩
    · cases h
  | node K j tcs =>
    simp only [leafOK, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hH, h⟩ := h
    simp only [Good, hH]
    split at h
    · rename_i d hd
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, beq_iff_eq] at h
      obtain ⟨hr, hp⟩ := h
      obtain ⟨n, hn, hs, hv⟩ := runTo_sound hT hr ρ
      rw [den_startS] at hs
      refine ⟨n, hn, d, List.mem_of_getElem? hd, _, hv, hs, ?_⟩
      intro hdH
      rcases hp with hp | ⟨p, hp, ht, hc⟩
      · rw [hp] at hdH; cases hdH
      · exact ⟨p, hp, ρ, by rw [ht, hc]⟩
    · cases h

theorem clsOK_sound {cl : List Cls} {pre : List PreE} {T : Tbl} (hT : T.OK) {c : Cls}
    (h : clsOK cl pre T c = true) : ∀ vs, ValidV vs c.res → Good cl pre c vs := by
  intro vs hv
  obtain ⟨ρ, hρ⟩ := rootC_onto 0 vs c.res hv
  rw [← hρ]
  exact chk_sound (Good cl pre c) (leafOK_sound hT c) c.tree (rootC 0 c.res) h ρ

/-! ## Halting if and only if a start of `pre` is reached -/

theorem steps_add (a b : Nat) (c : Config) :
    TM.steps trans (a + b) c = (TM.steps trans a c).bind (TM.steps trans b) := by
  induction a generalizing c with
  | zero => simp [TM.steps]
  | succ a ih =>
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [e]
    cases hs : TM.step trans c with
    | none => simp [TM.steps, hs]
    | some d =>
      rw [TM.steps_succ_of_step trans (a + b) hs, TM.steps_succ_of_step trans a hs]
      exact ih d

/-- A run to a halting configuration in `n` steps passes every configuration it reaches before. -/
theorem halt_after {c c' h : Config} {n m : Nat} (hn : steps n c = some h) (hh : step h = none)
    (hm : steps m c = some c') : m ≤ n ∧ steps (n - m) c' = some h := by
  change TM.steps trans n c = some h at hn
  change TM.steps trans m c = some c' at hm
  by_cases hle : m ≤ n
  · refine ⟨hle, ?_⟩
    have e := steps_add m (n - m) c
    rw [Nat.add_sub_cancel' hle, hn, hm] at e
    exact e.symm
  · have e : m = n + ((m - n - 1) + 1) := by omega
    have := TM.steps_halt trans hn hh (m - n - 1)
    rw [← e, hm] at this
    cases this

theorem halts_of_reach {a b : Config} (h : Reach a b) (hb : Halts trans b) : Halts trans a := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, c, hm, hc⟩ := hb
  exact ⟨n + m, c, steps_seq trans hn hm, hc⟩

section
variable {cl : List Cls} {pre : List PreE} {T : Tbl} (hT : T.OK) (hcl : ∀ c ∈ cl, clsOK cl pre T c = true)
include hT hcl

theorem reach_pre : ∀ N n, n ≤ N → ∀ c ∈ cl, ∀ vs, ValidV vs c.res → c.isH = false →
    (∃ h, steps n (nodeCfg c.text vs) = some h ∧ step h = none) →
    ∃ p ∈ pre, ∃ ρ, Reach (nodeCfg c.text vs) (nodeCfg p.text (evals ρ p.cs)) := by
  intro N
  induction N with
  | zero =>
    intro n hnN c hc vs hv hH ⟨h, hn, hh⟩
    have g := clsOK_sound hT (hcl c hc) vs hv
    simp only [Good, hH] at g
    obtain ⟨m, hm, d, hd, vs', hv', hs, hpre⟩ := g
    obtain ⟨hle, _⟩ := halt_after hn hh hs
    omega
  | succ N ih =>
    intro n hnN c hc vs hv hH ⟨h, hn, hh⟩
    have g := clsOK_sound hT (hcl c hc) vs hv
    simp only [Good, hH] at g
    obtain ⟨m, hm, d, hd, vs', hv', hs, hpre⟩ := g
    obtain ⟨hle, hrest⟩ := halt_after hn hh hs
    cases hdH : d.isH with
    | true =>
      obtain ⟨p, hp, ρ, e⟩ := hpre hdH
      exact ⟨p, hp, ρ, e ▸ Reach.refl _⟩
    | false =>
      obtain ⟨p, hp, ρ, hr⟩ := ih (n - m) (by omega) d hd vs' hv' hdH ⟨h, hrest, hh⟩
      exact ⟨p, hp, ρ, Reach.trans ⟨m, hs⟩ hr⟩

/-- **Halting if and only if a start of `pre` is reached**, from the checks: every class, every entry of `pre`,
and an arrival from blank tape at a node of a class that does not halt. -/
theorem halts_iff_of_checks (hpre : ∀ p ∈ pre, preOK cl T p = true)
    (harr : ∃ c ∈ cl, ∃ vs, ValidV vs c.res ∧ c.isH = false ∧ Reach init (nodeCfg c.text vs)) :
    HaltsFromBlank ↔ ∃ p ∈ pre, ∃ ρ, Reach init (nodeCfg p.text (evals ρ p.cs)) := by
  obtain ⟨c, hc, vs, hv, hH, n0, h0⟩ := harr
  constructor
  · rintro ⟨n, h, hn, hh⟩
    obtain ⟨_, hrest⟩ := halt_after hn hh h0
    obtain ⟨p, hp, ρ, hr⟩ := reach_pre hT hcl (n - n0) (n - n0) (Nat.le_refl _) c hc vs hv hH ⟨h, hrest, hh⟩
    exact ⟨p, hp, ρ, Reach.trans ⟨n0, h0⟩ hr⟩
  · rintro ⟨p, hp, ρ, hr⟩
    apply halts_of_reach hr
    have h := hpre p hp
    simp only [preOK] at h
    split at h
    · rename_i d hd
      simp only [Bool.and_eq_true] at h
      obtain ⟨hdH, hrun⟩ := h
      obtain ⟨m, _, hs, hv'⟩ := runTo_sound hT hrun ρ
      rw [den_startS] at hs
      have g := clsOK_sound hT (hcl d (List.mem_of_getElem? hd)) _ hv'
      simp only [Good, hdH, ite_true] at g
      exact halts_of_reach ⟨m, hs⟩ g
    · cases h

end

/-- The arrival: K moves of the executor from blank tape end at the node of class `j` with counts `vs`. -/
def arrives (cl : List Cls) (T : Tbl) (K j : Nat) (vs : List Nat) : Bool :=
  match cl[j]? with
  | some d => !d.isH &&
    match run T K ⟨[], [], .D⟩ with
    | some S' => atNode S' d (consts vs)
    | none => false
  | none => false

theorem arrives_sound {cl : List Cls} {T : Tbl} (hT : T.OK) {K j : Nat} {vs : List Nat}
    (h : arrives cl T K j vs = true) :
    ∃ c ∈ cl, ∃ vs, ValidV vs c.res ∧ c.isH = false ∧ Reach init (nodeCfg c.text vs) := by
  simp only [arrives] at h
  split at h
  · rename_i d hd
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hH, h⟩ := h
    split at h
    · rename_i S' hr
      have hr' := run_sound hT K hr (fun _ => 0)
      obtain ⟨e, hv⟩ := atNode_sound h (fun _ => 0)
      refine ⟨d, List.mem_of_getElem? hd, _, hv, hH, ?_⟩
      rw [← e]
      exact hr'
    · cases h
  · cases h

/-- **Halting if and only if a halting class is reached**: with the same checks, the machine halts from blank tape
if and only if its run reaches a node of a class marked `isH`. -/
theorem halts_iff_reach_H {cl : List Cls} {pre : List PreE} {T : Tbl} (hT : T.OK)
    (hcl : ∀ c ∈ cl, clsOK cl pre T c = true) (hpre : ∀ p ∈ pre, preOK cl T p = true)
    (harr : ∃ c ∈ cl, ∃ vs, ValidV vs c.res ∧ c.isH = false ∧ Reach init (nodeCfg c.text vs)) :
    HaltsFromBlank ↔ ∃ c ∈ cl, c.isH = true ∧ ∃ vs, ValidV vs c.res ∧ Reach init (nodeCfg c.text vs) := by
  rw [halts_iff_of_checks hT hcl hpre harr]
  constructor
  · rintro ⟨p, hp, ρ, hr⟩
    have h := hpre p hp
    simp only [preOK] at h
    split at h
    · rename_i d hd
      simp only [Bool.and_eq_true] at h
      obtain ⟨hdH, hrun⟩ := h
      obtain ⟨m, _, hs, hv'⟩ := runTo_sound hT hrun ρ
      rw [den_startS] at hs
      exact ⟨d, List.mem_of_getElem? hd, hdH, _, hv', Reach.trans hr ⟨m, hs⟩⟩
    · cases h
  · rintro ⟨c, hc, hH, vs, hv, hr⟩
    rw [← halts_iff_of_checks hT hcl hpre harr]
    have g := clsOK_sound hT (hcl c hc) vs hv
    simp only [Good, hH, ite_true] at g
    exact halts_of_reach hr g

end H163738M
