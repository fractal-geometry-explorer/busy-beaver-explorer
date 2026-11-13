import Sweep

/-!
# Many sweeps at once: the carry automaton as a group word, and a certificate checker for its powers

`carry` (in `Sweep.lean`) is one sweep.  Here the automaton is read as a transducer with an identity state: a word
`w` of generators applied to a digit string, one generator after the other, transforms the string digit by digit;
at each digit the word leaves a word of *sections* (the states the generators are in) that acts on the rest of the
string (`secW`, `trW`).  Applying `a^k` and getting an empty word of sections at the end means: none of the k
sweeps runs off the end of the digits, and then `sweeps k xs = some ys` (`sweeps_of_trW`).

The words involved are huge (`a^k` with k about 8·10^9), so they are kept as a straight-line program: a table of
nodes, each a generator or the concatenation of two earlier nodes (`val`).  A certificate lists, for some pairs
(node, digit), the digit the node turns it into and a node for the word of sections; `okAll` checks every listed
entry locally (a generator against the automaton; a concatenation against the entries of its two parts), and
`entry_sound` proves that every checked entry is right.  `chain` then follows the entries digit by digit
(`chain_sound`), and `okPow` checks claimed powers of `a` (`pow_sound`).
-/

namespace H74982

deriving instance DecidableEq for Q

/-- One generator on one digit: the new digit and the state it goes on in (`none`: the identity, the carry stops). -/
def act1 : Q → Bool → Bool × Option Q
  | .a, false => (true, none)
  | .a, true => (false, some .b)
  | .b, false => (true, some .a)
  | .b, true => (false, some .c)
  | .c, false => (false, some .c)
  | .c, true => (true, some .a)

/-- A word (applied first letter first) on one digit: the digit it ends as, and the word of sections. -/
def secW : List Q → Bool → Bool × List Q
  | [], x => (x, [])
  | g :: w, x => ((secW w (act1 g x).1).1, (act1 g x).2.toList ++ (secW w (act1 g x).1).2)

/-- A word on a digit string: the new string, and the word of sections left at its end. -/
def trW : List Q → List Bool → List Bool × List Q
  | w, [] => ([], w)
  | w, x :: xs => ((secW w x).1 :: (trW (secW w x).2 xs).1, (trW (secW w x).2 xs).2)

theorem secW_append (u v : List Q) (x : Bool) :
    secW (u ++ v) x = ((secW v (secW u x).1).1, (secW u x).2 ++ (secW v (secW u x).1).2) := by
  induction u generalizing x with
  | nil => simp [secW]
  | cons g u ih => simp [secW, ih, List.append_assoc]

theorem trW_nil (xs : List Bool) : trW [] xs = (xs, []) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [trW, secW, ih]

theorem trW_append (u v : List Q) (xs : List Bool) :
    trW (u ++ v) xs = ((trW v (trW u xs).1).1, (trW u xs).2 ++ (trW v (trW u xs).1).2) := by
  induction xs generalizing u v with
  | nil => simp [trW]
  | cons x xs ih => simp [trW, secW_append, ih]

/-- One generator with no sections left is one sweep that stops inside the digits. -/
theorem carry_of_trW (g : Q) (xs ys : List Bool) (h : trW [g] xs = (ys, [])) : carry g xs = some ys := by
  induction xs generalizing g ys with
  | nil => simp [trW] at h
  | cons x xs ih =>
    cases g <;> cases x <;> simp only [trW, secW, act1, Option.toList, List.append_nil,
      trW_nil, Prod.mk.injEq] at h <;> obtain ⟨rfl, h2⟩ := h
    · rfl
    · simp only [carry, ih _ _ (Prod.ext rfl h2), Option.map_some]
    · simp only [carry, ih _ _ (Prod.ext rfl h2), Option.map_some]
    · simp only [carry, ih _ _ (Prod.ext rfl h2), Option.map_some]
    · simp only [carry, ih _ _ (Prod.ext rfl h2), Option.map_some]
    · simp only [carry, ih _ _ (Prod.ext rfl h2), Option.map_some]

/-- k sweeps, each a carry that stops inside the digits. -/
def sweeps : Nat → List Bool → Option (List Bool)
  | 0, xs => some xs
  | k + 1, xs => (carry .a xs).bind (sweeps k)

theorem sweeps_of_trW (k : Nat) (xs ys : List Bool) (h : trW (List.replicate k .a) xs = (ys, [])) :
    sweeps k xs = some ys := by
  induction k generalizing xs with
  | zero => simpa [trW_nil, sweeps] using h
  | succ k ih =>
    rw [List.replicate_succ, show Q.a :: List.replicate k .a = [.a] ++ List.replicate k .a from rfl,
      trW_append] at h
    simp only [Prod.mk.injEq, List.append_eq_nil_iff] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp only [sweeps, carry_of_trW .a xs _ (Prod.ext rfl h2), Option.bind_some]
    exact ih _ (Prod.ext h1 h3)

/-! ## Straight-line programs and their certificates -/

/-- A node of a straight-line program: the empty word, a generator, or two earlier nodes one after the other. -/
inductive Node where
  | eps
  | gen (g : Q)
  | cat (i j : Nat)
  deriving DecidableEq

section
variable (T : Nat → Node)

/-- The word a node stands for (a child that is not earlier counts as empty; `okAll` rules that out). -/
def val (i : Nat) : List Q :=
  match T i with
  | .eps => []
  | .gen g => [g]
  | .cat j k => (if j < i then val j else []) ++ (if k < i then val k else [])
termination_by i
decreasing_by all_goals assumption

theorem val_eq (i : Nat) : val T i = match T i with
    | .eps => []
    | .gen g => [g]
    | .cat j k => (if j < i then val T j else []) ++ (if k < i then val T k else []) := by
  rw [val]

def isEps : Node → Bool
  | .eps => true
  | _ => false

theorem val_of_isEps {i : Nat} (h : isEps (T i) = true) : val T i = [] := by
  rw [val_eq]
  split <;> simp_all [isEps]

theorem val_of_gen {i : Nat} {g : Q} (h : T i = .gen g) : val T i = [g] := by
  rw [val_eq, h]

theorem val_of_cat {i j k : Nat} (h : T i = .cat j k) (hj : j < i) (hk : k < i) :
    val T i = val T j ++ val T k := by
  rw [val_eq, h]
  simp [hj, hk]

/-- `s` stands for the word `val i ++ val j`: it is their concatenation, or one of them is empty. -/
def isCat (s i j : Nat) : Bool :=
  (decide (T s = .cat i j) && decide (i < s) && decide (j < s)) ||
  (isEps (T i) && decide (s = j)) || (isEps (T j) && decide (s = i))

theorem val_of_isCat {s i j : Nat} (h : isCat T s i j = true) : val T s = val T i ++ val T j := by
  simp only [isCat, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with (⟨⟨h1, h2⟩, h3⟩ | ⟨h1, rfl⟩) | ⟨h1, rfl⟩
  · exact val_of_cat T h1 h2 h3
  · simp [val_of_isEps T h1]
  · simp [val_of_isEps T h1]

/-- `s` stands for the word of an optional generator. -/
def isOpt (s : Nat) : Option Q → Bool
  | none => isEps (T s)
  | some g => decide (T s = .gen g)

theorem val_of_isOpt {s : Nat} {o : Option Q} (h : isOpt T s o = true) : val T s = o.toList := by
  cases o with
  | none => exact val_of_isEps T h
  | some g => exact val_of_gen T (of_decide_eq_true h)

variable (E : Nat → Bool → Option (Nat × Bool))

/-- The local check of the entry for node i and digit x (if there is one). -/
def okEnt (i : Nat) (x : Bool) : Bool :=
  match E i x with
  | none => true
  | some (s, y) =>
    match T i with
    | .eps => decide (y = x) && isEps (T s)
    | .gen g => decide ((act1 g x).1 = y) && isOpt T s (act1 g x).2
    | .cat j k =>
      decide (j < i) && decide (k < i) &&
      match E j x with
      | none => false
      | some (s1, x1) =>
        match E k x1 with
        | none => false
        | some (s2, y2) => decide (y2 = y) && isCat T s s1 s2

def okAll (N : Nat) : Bool :=
  (List.range N).all fun i => okEnt T E i false && okEnt T E i true

/-- Every entry that passes the check is right: the node's word turns x into y and leaves the word of node s. -/
theorem entry_sound (N : Nat) (hok : okAll T E N = true) (hN : ∀ i x e, E i x = some e → i < N) :
    ∀ i x s y, E i x = some (s, y) → secW (val T i) x = (y, val T s) := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro x s y he
    have hi : okEnt T E i x = true := by
      have := List.all_eq_true.mp hok i (List.mem_range.mpr (hN i x _ he))
      cases x <;> simp_all
    unfold okEnt at hi
    rw [he] at hi
    simp only at hi
    revert hi
    rw [val_eq]
    split
    · next h =>
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      rintro ⟨rfl, h2⟩
      simp [secW, val_of_isEps T h2]
    · next g h =>
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      rintro ⟨h1, h2⟩
      simp [secW, ← h1, val_of_isOpt T h2]
    · next j k h =>
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      rintro ⟨⟨hj, hk⟩, h3⟩
      split at h3
      · cases h3
      · next s1 x1 e1 =>
        split at h3
        · cases h3
        · next s2 y2 e2 =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
          obtain ⟨rfl, h4⟩ := h3
          simp only [hj, hk, ite_true, secW_append, ih j hj x s1 x1 e1, ih k hk x1 s2 y2 e2,
            val_of_isCat T h4]

/-- Follow the entries digit by digit from node n until a node is empty (`none` if an entry is missing or the
digits run out first). -/
def chain : Nat → List Bool → Option (List Bool)
  | n, [] => if isEps (T n) then some [] else none
  | n, x :: xs =>
    if isEps (T n) then some (x :: xs) else
      match E n x with
      | none => none
      | some (s, y) => (chain s xs).map (y :: ·)

theorem chain_sound (N : Nat) (hok : okAll T E N = true) (hN : ∀ i x e, E i x = some e → i < N)
    (n : Nat) (xs ys : List Bool) (h : chain T E n xs = some ys) : trW (val T n) xs = (ys, []) := by
  induction xs generalizing n ys with
  | nil =>
    simp only [chain] at h
    split at h
    · next he => cases h; rw [val_of_isEps T he]; rfl
    · cases h
  | cons x xs ih =>
    simp only [chain] at h
    split at h
    · next he => cases h; rw [val_of_isEps T he, trW_nil]
    · split at h
      · cases h
      · next s y e =>
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨zs, h1, rfl⟩ := h
        have h2 := entry_sound T E N hok hN n x s y e
        simp only [trW, h2, ih s zs h1]

/-- Claimed powers of `a`: (node, exponent) pairs.  A pair is checked against the node and the pairs of its parts
(a lookup, so shared parts are checked once). -/
def okPow (lens : List (Nat × Nat)) (i m : Nat) : Bool :=
  match T i with
  | .gen .a => decide (m = 1)
  | .cat j k =>
    decide (j < i) && decide (k < i) &&
    match lens.lookup j, lens.lookup k with
    | some m1, some m2 => decide (m = m1 + m2)
    | _, _ => false
  | _ => false

theorem lookup_mem {lens : List (Nat × Nat)} {j m : Nat} (h : lens.lookup j = some m) : (j, m) ∈ lens := by
  induction lens with
  | nil => cases h
  | cons p ps ih =>
    obtain ⟨j', m'⟩ := p
    simp only [List.lookup] at h
    by_cases e : j = j'
    · subst e
      simp at h
      subst h
      exact List.mem_cons_self
    · simp [show (j == j') = false from by simpa using e] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem pow_sound (lens : List (Nat × Nat)) (hok : lens.all (fun p => okPow T lens p.1 p.2) = true) :
    ∀ i m, (i, m) ∈ lens → val T i = List.replicate m .a := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro m hm
    have h := List.all_eq_true.mp hok (i, m) hm
    simp only [okPow] at h
    split at h
    · next he => simp only [decide_eq_true_eq] at h; subst h; exact val_of_gen T he
    · next j k he =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hj, hk⟩, h3⟩ := h
      split at h3
      · next m1 m2 e1 e2 =>
        simp only [decide_eq_true_eq] at h3
        subst h3
        rw [val_of_cat T he hj hk, ih j hj m1 (lookup_mem e1), ih k hk m2 (lookup_mem e2),
          List.replicate_append_replicate]
      · cases h3
    · cases h

end

end H74982
