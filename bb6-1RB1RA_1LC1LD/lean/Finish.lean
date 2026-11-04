import Recur

/-!
# The recursive pass cannot go round in circles

The block machine of `Recur.lean` has a quantity that goes down at every step.  Take the cells from the head to the
right end of the tape (`cells`: the ones under the head, then the words `0 1^k`) and read them from the right end
(`key`).  Every step of `astep` that does not end the pass makes this list smaller in dictionary order, with a 1 before
a 0 and a list before its extensions (`astep_key`).  Either the step moves the head right past whole words, so `key`
loses its last cells, or the first word it changes, counting from the right end, gets longer, so a 0 of `key` turns
into a 1 with nothing changed before it.

So the block machine never repeats a configuration.  Dictionary order on lists of any length has infinite descending
chains (`0`, `10`, `110`, … ), so this alone does not make the pass finish; it does as soon as `key` has bounded
length, that is, as long as the head stays within `N` cells of the right end: then the pass ends within `3^N` steps
of the block machine, or the block machine meets a case it does not cover (`arun_finishes`, `pass_finishes`).  What
this leaves open is that the head does not drift left without bound.
-/

namespace BB6c

/-! ## Dictionary order on bit lists -/

/-- `l₁` comes before `l₂` in dictionary order with `false` before `true`, a proper prefix first. -/
inductive Below : List Bool → List Bool → Prop
  | nil {b : Bool} {l : List Bool} : Below [] (b :: l)
  | bit {l₁ l₂ : List Bool} : Below (false :: l₁) (true :: l₂)
  | cons {b : Bool} {l₁ l₂ : List Bool} : Below l₁ l₂ → Below (b :: l₁) (b :: l₂)

theorem Below.app (p : List Bool) {s t : List Bool} (h : Below s t) : Below (p ++ s) (p ++ t) := by
  induction p with
  | nil => exact h
  | cons b p ih => exact .cons ih

theorem below_pop (b : Bool) (t X : List Bool) : Below X.reverse ((b :: t) ++ X).reverse := by
  rw [List.reverse_append]
  have := Below.app X.reverse (Below.nil (b := (b :: t).reverse.head (by simp)) (l := (b :: t).reverse.tail))
  rwa [List.append_nil, List.cons_head_tail] at this

theorem below_grow (s s' : List Bool) {k m : Nat} (hm : k + 1 ≤ m) (X : List Bool) :
    Below (s' ++ (List.replicate m false ++ X)).reverse (s ++ (true :: (List.replicate k false ++ X))).reverse := by
  obtain ⟨d, rfl⟩ : ∃ d, m = (d + 1) + k := ⟨m - (k + 1), by omega⟩
  rw [← List.replicate_append_replicate (n := d + 1) (m := k)]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate, List.append_assoc, List.cons_append,
    List.nil_append]
  rw [List.replicate_succ]
  exact Below.app _ (Below.app _ .bit)

def val : Nat → List Bool → Nat
  | 0, _ => 0
  | _ + 1, [] => 0
  | N + 1, b :: l => (if b then 2 else 1) * 3 ^ N + val N l

theorem val_lt : ∀ (N : Nat) (l : List Bool), val N l < 3 ^ N
  | 0, _ => by simp [val]
  | N + 1, [] => by simp [val]; exact Nat.pow_pos (by decide)
  | N + 1, b :: l => by
    have := val_lt N l
    cases b <;> simp [val, Nat.pow_succ] <;> omega

theorem val_mono {l₁ l₂ : List Bool} (h : Below l₁ l₂) : ∀ {N : Nat}, l₂.length ≤ N → val N l₁ < val N l₂ := by
  induction h with
  | nil => intro N hN; cases N with
    | zero => simp at hN
    | succ N => rename_i b l; have := Nat.pow_pos (a := 3) (n := N) (by decide); cases b <;> simp [val] <;> omega
  | bit => intro N hN; cases N with
    | zero => simp at hN
    | succ N => rename_i l₁ l₂; have := val_lt N l₁; simp [val]; omega
  | cons h ih => intro N hN; cases N with
    | zero => simp at hN
    | succ N => rename_i b _ _; have := @ih N (by simp at hN; omega); cases b <;> simp [val] <;> omega

/-! ## The key -/

/-- The cells of the words `0 1^k`, left to right, a 1 as `false` and a 0 as `true`. -/
def wc : List Nat → List Bool
  | [] => []
  | k :: W => true :: (List.replicate k false ++ wc W)

/-- The cells from the head to the right end of the tape. -/
def cells (c : ACfg) : List Bool := List.replicate c.h false ++ wc c.W

/-- The same, read from the right end. -/
def key (c : ACfg) : List Bool := (cells c).reverse

/-- The words `tw a j k` end with one of at least `k + 1` ones. -/
theorem wc_tw (X : List Nat) (k : Nat) : ∀ (j a : Nat), 1 ≤ a →
    ∃ s m, k + 1 ≤ m ∧ wc (tw a j k ++ X) = s ++ (List.replicate m false ++ wc X)
  | 0, a, ha => ⟨[true], a + k, by omega, rfl⟩
  | j + 1, a, _ => by
    obtain ⟨s, m, hm, e⟩ := wc_tw X k j 2 (by decide)
    refine ⟨true :: (List.replicate a false ++ s), m, hm, ?_⟩
    show true :: (List.replicate a false ++ wc (tw 2 j k ++ X)) = _
    rw [e]; simp only [List.cons_append, List.append_assoc]

/-- A step that moves the head right past the ones under it. -/
theorem key_pop_h {c c' : ACfg} (h₁ : c'.h = 0) (h₂ : c'.W = c.W) (h₃ : 0 < c.h) : Below (key c') (key c) := by
  obtain ⟨h, e⟩ : ∃ h, c.h = h + 1 := ⟨c.h - 1, by omega⟩
  unfold key cells; rw [h₁, h₂, e]; exact below_pop false _ _

/-- A step that moves the head right past the ones under it and the next word. -/
theorem key_pop_word {c c' : ACfg} {w : Nat} (h₁ : c'.h = 0) (h₂ : c.W = w :: c'.W) : Below (key c') (key c) := by
  unfold key cells; rw [h₁, h₂]
  cases c.h with
  | zero => exact below_pop true _ _
  | succ h =>
    show Below _ (List.reverse (false :: (List.replicate h false ++ wc (w :: c'.W))))
    rw [show false :: (List.replicate h false ++ wc (w :: c'.W)) =
      (false :: (List.replicate h false ++ true :: List.replicate w false)) ++ wc c'.W by simp [wc]]
    exact below_pop false _ _

/-- A step that lengthens a word `0 1^k` with only the words left of it changed. -/
theorem key_grow {c c' : ACfg} (s s' X : List Bool) {k m : Nat} (hm : k + 1 ≤ m)
    (h₁ : cells c' = s' ++ (List.replicate m false ++ X)) (h₂ : cells c = s ++ (true :: (List.replicate k false ++ X))) :
    Below (key c') (key c) := by
  unfold key; rw [h₁, h₂]; exact below_grow s s' hm X

theorem key_grow_tw {c c' : ACfg} (s₀ s : List Bool) {a j k : Nat} {W : List Nat} (ha : 1 ≤ a)
    (h₁ : cells c' = s₀ ++ wc (tw a j k ++ W)) (h₂ : cells c = s ++ (true :: (List.replicate k false ++ wc W))) :
    Below (key c') (key c) := by
  obtain ⟨s', m, hm, e⟩ := wc_tw W k j a ha
  exact key_grow s (s₀ ++ s') (wc W) hm (by rw [h₁, e, List.append_assoc]) h₂

theorem bstep_key {n c d k : Nat} {M W : List Nat} {c' : ACfg} (e : bstep n c d M k W = some (.go c')) :
    Below (key c') (key ⟨.B, 0, n :: c :: d :: M, k :: W⟩) := by
  have old : cells ⟨.B, 0, n :: c :: d :: M, k :: W⟩ = [] ++ (true :: (List.replicate k false ++ wc W)) := rfl
  unfold bstep at e
  split at e
  · cases e; exact key_grow_tw [true] [] (by decide) rfl old
  split at e
  · cases e; exact key_grow [] [] (wc W) (Nat.le_refl _) rfl old
  split at e
  · cases e; exact key_grow_tw [false] [] (by decide) rfl old
  split at e
  · cases e; subst k; exact key_grow_tw [] [] (by decide) rfl old
  split at e
  · cases e; exact key_grow [] [true] (wc W) (Nat.le_refl _) rfl old
  split at e
  · cases e; exact key_grow [] [] (wc W) (Nat.le_refl _) rfl old
  · cases e; exact key_grow_tw [false] [] (by decide) rfl old

/-- C moves a block into the word after `0 1`. -/
theorem key_cmove (c k : Nat) (M W : List Nat) :
    Below (key ⟨.C, 0, 0 :: M, 1 :: (k + c + 1) :: W⟩) (key ⟨.C, 0, (c + 1) :: M, 1 :: k :: W⟩) :=
  key_grow [true, false] [true, false, true] (wc W) (m := k + c + 1) (by omega) rfl rfl

theorem astep'_key {q : St} {h : Nat} {L W : List Nat} {c' : ACfg} (e : astep' q h L W = some (.go c')) :
    Below (key c') (key ⟨q, h, L, W⟩) := by
  unfold astep' at e
  split at e <;> (try cases e)
  · exact key_pop_h rfl rfl (Nat.succ_pos _)
  · exact key_pop_word rfl rfl
  · exact key_pop_word rfl rfl
  · exact key_pop_word rfl rfl
  · exact key_pop_word rfl rfl
  · exact key_pop_word rfl rfl
  · exact key_pop_word rfl rfl
  · exact key_pop_word rfl rfl
  · exact key_pop_word rfl rfl
  · exact key_cmove _ _ _ _
  · exact key_pop_word rfl rfl
  · exact key_pop_word rfl rfl
  · exact key_pop_word rfl rfl
  · exact bstep_key e

/-- **Every step of the block machine that does not end the pass lowers `key`** (kernel only). -/
theorem astep_key {c c' : ACfg} (e : astep c = some (.go c')) : Below (key c') (key c) :=
  astep'_key (q := c.q) (h := c.h) (L := pad 4 c.L) (W := c.W) e

/-! ## Bounded, the pass finishes -/

/-- `n` steps of the block machine, if none of them ends the pass. -/
def agos : Nat → ACfg → Option ACfg
  | 0, c => some c
  | n + 1, c =>
    match astep c with
    | some (.go c') => agos n c'
    | _ => none

theorem arun_finishes_of {N : Nat} : ∀ (f : Nat) {c : ACfg},
    (∀ n c', agos n c = some c' → (key c').length ≤ N ∧ astep c' ≠ none) → val N (key c) < f →
      ∃ o, arun f c = some o := by
  intro f
  induction f with
  | zero => intro c _ h; cases h
  | succ f ih =>
    intro c hb hf
    obtain ⟨hl, hs⟩ := hb 0 c rfl
    unfold arun
    match e : astep c with
    | none => exact absurd e hs
    | some (.go c') =>
      simp only
      have hb' : ∀ n c'', agos n c' = some c'' → (key c'').length ≤ N ∧ astep c'' ≠ none :=
        fun n c'' h => hb (n + 1) c'' (by simp only [agos, e]; exact h)
      have := val_mono (astep_key e) hl
      exact ih hb' (by omega)
    | some (.pass _ _) => exact ⟨_, rfl⟩
    | some .halt => exact ⟨_, rfl⟩

/-- **If the head stays within `N` cells of the right end and the block machine never meets a case it does not
cover, it ends the pass within `3^N` steps** (kernel only). -/
theorem arun_finishes {N : Nat} {c : ACfg}
    (hb : ∀ n c', agos n c = some c' → (key c').length ≤ N ∧ astep c' ≠ none) : ∃ o, arun (3 ^ N) c = some o :=
  arun_finishes_of _ hb (val_lt N _)

/-- The recursive pass from `K ls n`, `n = 3j + 2`, with the same conditions on the block machine from `k_start`:
`pass` gives the next pass start or a halt, and by `pass_sound` the machine does what it gives. -/
theorem pass_finishes {N : Nat} {ls : List Nat} {n : Nat}
    (hb : ∀ k c', agos k ⟨.B, 0, pad 1 ls, 0 :: 1 :: tw 2 (n / 3) 0⟩ = some c' →
      (key c').length ≤ N ∧ astep c' ≠ none) :
    n % 3 = 2 → ∃ o, pass (3 ^ N) ls n = some o := by
  intro hn
  unfold pass
  split
  · exact ⟨_, rfl⟩
  · simp only [show n ≠ 0 by omega, hn, ite_false, ite_true]; exact arun_finishes hb

end BB6c
