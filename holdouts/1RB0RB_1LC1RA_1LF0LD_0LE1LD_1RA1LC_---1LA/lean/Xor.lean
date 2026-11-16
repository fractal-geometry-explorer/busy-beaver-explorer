/-!
# The XOR sweep (machine-independent)

The four machines of family F08 that share the `111110` block (`1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA`,
`1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA`, `1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA`,
`1RB1LD_1RC0RC_1LD1RB_1LF0LE_0LA1LE_---1LB`) read, at each turn at the right end of the tape, a word over pairs
(`11` = 1, `01` = 0).  This file is about that word alone; each machine's `Bits.lean` proves that its pass machine
does exactly what is described here.

The word is kept **reversed**: `r` is the word read from the right end of the tape (the head) to the left end.
One sweep (`swr r`): find the first `0 0` of `r` (the rightmost `00` of the tape); everything before it is replaced
by its XOR differences, the letter after it is flipped, and the word gains `1 1` at the head.  No `00` at all is a
*reset* (the pass runs off the left end, a machine-dependent event), a `00` at the very end of `r` a *halt*.

* `swr_append_ok`: a sweep that finds its `00` inside a prefix does not touch the rest of the word
  (a zone further left is **frozen**);
* `swr_halt_snoc`: a `00` at the end of a prefix flips only the next letter;
* `swr_split`: a pass through a stretch `P` without `00` changes `P` into `xd P`, and what it does beyond `P`
  depends only on the last letter of `P` (the **pass-through** lemma);
* `zone_step`: with the block of words at the head (`blk`), the sweep is the same for **every length** of the
  block, with only the length mod 3 entering, through one letter (`pat`): the leftmost zone is a finite system with
  a period-3 input (the **zone reduction**);
* `xd_append`: the XOR differences over a suffix `b :: t` are `xd (b :: t)`, whatever stands before it (the light
  cone: a letter changes only through itself and its right neighbour on the tape).

Everything is checked by Lean's kernel.
-/

namespace XS

/-- XOR differences of neighbours: `[a₀ ⊕ a₁, a₁ ⊕ a₂, …]`, one letter shorter. -/
def xd : List Bool → List Bool
  | a :: b :: t => (a != b) :: xd (b :: t)
  | _ => []

/-- Outcome of a sweep: `ok d X` means the new reversed word is `true :: true :: X`, the `00` having been found
after `d` letters. -/
inductive SW where
  | ok (d : Nat) (X : List Bool)
  | halt
  | reset
  deriving DecidableEq, Repr

/-- Put letters in front of the `X` of an outcome. -/
def SW.pre (L : List Bool) : SW → SW
  | .ok d X => .ok (d + L.length) (L ++ X)
  | s => s

/-- One sweep of the reversed word. -/
def swr : List Bool → SW
  | false :: false :: c :: t => .ok 0 (false :: (!c) :: t)
  | [false, false] => .halt
  | a :: b :: t => (swr (b :: t)).pre [a != b]
  | _ => .reset

/-- No two neighbouring `0`s. -/
def nozz : List Bool → Bool
  | false :: false :: _ => false
  | _ :: t => nozz t
  | [] => true

theorem SW.pre_nil (s : SW) : s.pre [] = s := by cases s <;> rfl

theorem SW.pre_pre (L M : List Bool) (s : SW) : (s.pre M).pre L = s.pre (L ++ M) := by
  cases s <;> simp [SW.pre, List.append_assoc]; omega

theorem swr_cons (a b : Bool) (t : List Bool) (h : ¬(a = false ∧ b = false)) :
    swr (a :: b :: t) = (swr (b :: t)).pre [a != b] := by
  cases a <;> cases b <;> simp_all [swr]

theorem SW.pre_eq_ok {L X : List Bool} {d : Nat} {s : SW} (h : s.pre L = .ok d X) :
    ∃ d' X', s = .ok d' X' ∧ X = L ++ X' ∧ d = d' + L.length := by
  cases s with
  | ok d' X' => simp only [SW.pre, SW.ok.injEq] at h; exact ⟨d', X', rfl, h.2.symm, h.1.symm⟩
  | halt => simp [SW.pre] at h
  | reset => simp [SW.pre] at h

/-! ## Frozen zones -/

/-- A sweep that is decided inside a prefix leaves the rest of the word alone. -/
theorem swr_append_ok : ∀ (Y R X : List Bool) (d : Nat), swr Y = .ok d X → swr (Y ++ R) = .ok d (X ++ R)
  | [], _, _, _, h => by simp [swr] at h
  | [a], _, _, _, h => by cases a <;> simp [swr] at h
  | [false, false], _, _, _, h => by simp [swr] at h
  | false :: false :: c :: t, R, X, d, h => by
    simp only [swr, SW.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | true :: b :: t, R, X, d, h => by
    rw [swr_cons _ _ _ (by simp)] at h
    obtain ⟨d', X', h1, rfl, rfl⟩ := SW.pre_eq_ok h
    rw [List.cons_append, List.cons_append, swr_cons _ _ _ (by simp), ← List.cons_append,
      swr_append_ok (b :: t) R X' d' h1]; rfl
  | false :: true :: t, R, X, d, h => by
    rw [swr_cons _ _ _ (by simp)] at h
    obtain ⟨d', X', h1, rfl, rfl⟩ := SW.pre_eq_ok h
    rw [List.cons_append, List.cons_append, swr_cons _ _ _ (by simp), ← List.cons_append,
      swr_append_ok (true :: t) R X' d' h1]; rfl

theorem SW.pre_eq_halt {L : List Bool} {s : SW} (h : s.pre L = .halt) : s = .halt := by
  cases s <;> simp_all [SW.pre]

theorem SW.pre_eq_reset {L : List Bool} {s : SW} (h : s.pre L = .reset) : s = .reset := by
  cases s <;> simp_all [SW.pre]

/-- A `00` at the very end of a prefix: the sweep goes on into the next letter only to flip it. -/
theorem swr_halt_snoc : ∀ (Y : List Bool) (c : Bool), swr Y = .halt → ∃ d X, swr (Y ++ [c]) = .ok d X
  | [], _, h => by simp [swr] at h
  | [a], _, h => by cases a <;> simp [swr] at h
  | [false, false], c, _ => ⟨_, _, rfl⟩
  | false :: false :: d :: t, _, h => by simp [swr] at h
  | true :: b :: t, c, h => by
    rw [swr_cons _ _ _ (by simp)] at h
    obtain ⟨d, X, hX⟩ := swr_halt_snoc (b :: t) c (SW.pre_eq_halt h)
    exact ⟨_, _, by rw [List.cons_append, List.cons_append, swr_cons _ _ _ (by simp), ← List.cons_append, hX]; rfl⟩
  | false :: true :: t, c, h => by
    rw [swr_cons _ _ _ (by simp)] at h
    obtain ⟨d, X, hX⟩ := swr_halt_snoc (true :: t) c (SW.pre_eq_halt h)
    exact ⟨_, _, by rw [List.cons_append, List.cons_append, swr_cons _ _ _ (by simp), ← List.cons_append, hX]; rfl⟩

/-! ## Passing through a stretch without `00` -/

theorem nozz_cons {a b : Bool} {t : List Bool} (h : nozz (a :: b :: t) = true) :
    ¬(a = false ∧ b = false) ∧ nozz (b :: t) = true := by
  cases a <;> cases b <;> simp_all [nozz]

/-- **Pass-through.** A sweep that crosses a stretch `P ++ [c]` without `00` turns it into its XOR differences;
what it does beyond depends only on the last letter `c`. -/
theorem swr_split : ∀ (P : List Bool) (c : Bool) (Z : List Bool), nozz (P ++ [c]) = true →
    swr (P ++ c :: Z) = (swr (c :: Z)).pre (xd (P ++ [c]))
  | [], c, Z, _ => by simp [xd, SW.pre_nil]
  | [a], c, Z, h => by
    have h1 := (nozz_cons (t := []) h).1
    show swr (a :: c :: Z) = _
    rw [swr_cons _ _ _ h1]; rfl
  | a :: b :: P, c, Z, h => by
    have h' := nozz_cons (t := P ++ [c]) h
    show swr (a :: b :: (P ++ c :: Z)) = _
    rw [swr_cons _ _ _ h'.1, ← List.cons_append, swr_split (b :: P) c Z h'.2, SW.pre_pre]; rfl

/-! ## The block of words -/

/-- The pattern of the block, read from the head: `1 1 0 1 1 0 …`. -/
def pat (k : Nat) : Bool := k % 3 != 2

/-- `n` letters of the pattern starting at `s`. -/
def blkFrom (s : Nat) : Nat → List Bool
  | 0 => []
  | n + 1 => pat s :: blkFrom (s + 1) n

/-- The block of words at the head of the reversed word, `n` letters long. -/
def blk (n : Nat) : List Bool := blkFrom 0 n

theorem pat_xor (s : Nat) : (pat s != pat (s + 1)) = pat (s + 2) := by
  unfold pat
  have h := Nat.mod_lt s (show 3 > 0 by omega)
  rcases (show s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 by omega) with h0 | h0 | h0 <;>
  · have h1 : (s + 1) % 3 = (s % 3 + 1) % 3 := by omega
    have h2 : (s + 2) % 3 = (s % 3 + 2) % 3 := by omega
    rw [h1, h2, h0]; rfl

theorem pat_mod (s : Nat) : pat s = pat (s % 3) := by
  unfold pat; rw [Nat.mod_mod]

theorem blkFrom_snoc : ∀ (s n : Nat), blkFrom s (n + 1) = blkFrom s n ++ [pat (s + n)]
  | s, 0 => rfl
  | s, n + 1 => by
    show pat s :: blkFrom (s + 1) (n + 1) = pat s :: (blkFrom (s + 1) n ++ _)
    rw [blkFrom_snoc (s + 1) n, show s + 1 + n = s + (n + 1) by omega]

theorem xd_blkFrom : ∀ (s n : Nat), xd (blkFrom s (n + 1)) = blkFrom (s + 2) n
  | s, 0 => rfl
  | s, n + 1 => by
    show (pat s != pat (s + 1)) :: xd (blkFrom (s + 1) (n + 1)) = pat (s + 2) :: blkFrom (s + 2 + 1) n
    rw [pat_xor, xd_blkFrom (s + 1) n, show s + 1 + 2 = s + 2 + 1 by omega]

theorem nozz_blkFrom : ∀ (s n : Nat), nozz (blkFrom s n) = true
  | s, 0 => rfl
  | s, 1 => by show nozz [pat s] = true; cases pat s <;> rfl
  | s, n + 2 => by
    show nozz (pat s :: pat (s + 1) :: blkFrom (s + 2) n) = true
    have ih := nozz_blkFrom (s + 1) (n + 1)
    have hp : ¬(pat s = false ∧ pat (s + 1) = false) := by
      unfold pat
      intro ⟨h1, h2⟩
      simp only [bne_eq_false_iff_eq] at h1 h2
      omega
    revert ih hp
    show nozz (pat (s + 1) :: blkFrom (s + 2) n) = true → _ → _
    cases pat s <;> cases pat (s + 1) <;> simp [nozz]

theorem blkFrom_length : ∀ (s n : Nat), (blkFrom s n).length = n
  | _, 0 => rfl
  | s, n + 1 => by simp [blkFrom, blkFrom_length (s + 1) n]

theorem blk_succ_succ (n : Nat) : blk (n + 2) = true :: true :: blkFrom 2 n := rfl

/-- **The zone reduction.** With the block of words (any length `n + 1`) at the head of the reversed word and any
word `Z` after it, the sweep acts on `Z` as the sweep of `pat n :: Z` does, and the block grows by one letter.  Only
`n mod 3` enters (`pat_mod`): the length of the block does not matter. -/
theorem zone_step (n : Nat) (Z : List Bool) : swr (blk (n + 1) ++ Z) = (swr (pat n :: Z)).pre (blkFrom 2 n) := by
  have h := swr_split (blkFrom 0 n) (pat n) Z
    (by rw [show [pat n] = [pat (0 + n)] by rw [Nat.zero_add], ← blkFrom_snoc]; exact nozz_blkFrom 0 (n + 1))
  rw [show blkFrom 0 n ++ [pat n] = blkFrom 0 (n + 1) by rw [blkFrom_snoc, Nat.zero_add]] at h
  unfold blk
  rw [blkFrom_snoc, Nat.zero_add, List.append_assoc, List.singleton_append, h, xd_blkFrom]

/-! ## Lengths and the light cone -/

theorem swr_length : ∀ (r X : List Bool) (d : Nat), swr r = .ok d X → X.length + 1 = r.length
  | [], _, _, h => by simp [swr] at h
  | [a], _, _, h => by cases a <;> simp [swr] at h
  | [false, false], _, _, h => by simp [swr] at h
  | false :: false :: c :: t, X, d, h => by simp only [swr, SW.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | true :: b :: t, X, d, h => by
    rw [swr_cons _ _ _ (by simp)] at h
    obtain ⟨d', X', h1, rfl, rfl⟩ := SW.pre_eq_ok h
    have := swr_length (b :: t) X' d' h1; simp_all
  | false :: true :: t, X, d, h => by
    rw [swr_cons _ _ _ (by simp)] at h
    obtain ⟨d', X', h1, rfl, rfl⟩ := SW.pre_eq_ok h
    have := swr_length (true :: t) X' d' h1; simp_all

theorem xd_append : ∀ (l : List Bool) (b : Bool) (t : List Bool), xd (l ++ b :: t) = xd (l ++ [b]) ++ xd (b :: t)
  | [], b, t => rfl
  | [a], b, t => rfl
  | a :: c :: l, b, t => by
    show (a != c) :: xd (c :: l ++ b :: t) = ((a != c) :: xd (c :: l ++ [b])) ++ _
    rw [xd_append (c :: l) b t]; rfl

/-- **The light cone.** XOR differences of `l ++ s`: the part over `s` is `xd s`; with `s` of length `k + 1`, the last
`k` letters of `xd (l ++ s)` depend only on `s`. -/
theorem xd_suffix (l : List Bool) (b : Bool) (t : List Bool) : ∃ u, xd (l ++ b :: t) = u ++ xd (b :: t) :=
  ⟨_, xd_append l b t⟩

end XS
