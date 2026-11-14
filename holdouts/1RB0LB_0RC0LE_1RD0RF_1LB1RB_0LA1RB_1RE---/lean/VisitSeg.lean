import VisitCheck

/-!
# The checker in segments

`check (a + b) s` can be evaluated in two parts (`check_add`), and the word in between can be written down as a
number (`dec len n`: the `len` low bits of `n`, lowest first).  So a long run is a chain of short evaluations.
-/

namespace VisitLaw

/-- Push the `k` low bits of `c`, lowest first, onto `acc` (which is reversed). -/
def pushBits : Nat → Nat → List Bool → List Bool
  | 0, _, acc => acc
  | k + 1, c, acc => pushBits k (c / 2) ((c % 2 == 1) :: acc)

/-- The `len` low bits of `n`, lowest first, reversed onto `acc`; 1024 bits at a time. -/
def decGo : Nat → Nat → Nat → List Bool → List Bool
  | 0, _, _, acc => acc
  | fuel + 1, len, n, acc =>
    if len = 0 then acc
    else if len ≤ 1024 then pushBits len n acc
    else decGo fuel (len - 1024) (n >>> 1024) (pushBits 1024 (n % 2 ^ 1024) acc)

/-- The `len` low bits of `n`, lowest first. -/
def dec (len n : Nat) : List Bool := (decGo (len + 1) len n []).reverse

/-- The number whose bits are the first `k` cells of the word, lowest first, and the rest of the word. -/
def takeBits : Nat → List Bool → Nat → Nat → Nat × List Bool
  | 0, s, a, _ => (a, s)
  | _ + 1, [], a, _ => (a, [])
  | k + 1, b :: t, a, w => takeBits k t (if b then a + w else a) (2 * w)

/-- The word as a list of 1024-bit numbers, highest chunk first. -/
def chunks : Nat → List Bool → List Nat → List Nat
  | 0, _, acc => acc
  | _ + 1, [], acc => acc
  | fuel + 1, s, acc => let p := takeBits 1024 s 0 1; chunks fuel p.2 (p.1 :: acc)

/-- The number whose bits are the word, lowest first. -/
def enc (s : List Bool) : Nat := (chunks (s.length + 1) s []).foldl (fun a c => (a <<< 1024) + c) 0

/-- `k` rounds take the word `s` to the word `dec lb b`. -/
def segFrom (k : Nat) (s : List Bool) (lb b : Nat) : Bool :=
  match iter k s with
  | some t => t == dec lb b
  | none => false

/-- `k` rounds take the word `dec la a` to the word `dec lb b`. -/
def seg (k la a lb b : Nat) : Bool := segFrom k (dec la a) lb b

theorem segFrom_sound {k lb b : Nat} {s : List Bool} (h : segFrom k s lb b = true) : iter k s = some (dec lb b) := by
  unfold segFrom at h
  split at h
  · rename_i t ht
    rw [ht, eq_of_beq h]
  · cases h

theorem seg_sound {k la a lb b : Nat} (h : seg k la a lb b = true) : iter k (dec la a) = some (dec lb b) :=
  segFrom_sound h

theorem iter_add {a b : Nat} {s t : List Bool} (h : iter a s = some t) : iter (b + a) s = iter b t := by
  induction a generalizing s with
  | zero => cases h; rfl
  | succ a ih =>
    unfold iter at h
    split at h
    · rename_i s' hs
      have e : iter (b + a + 1) s = iter (b + a) s' := by
        show (match round s with | some s' => iter (b + a) s' | none => none) = _
        rw [hs]
      exact e.trans (ih h)
    · cases h

theorem check_add {a b : Nat} {s t : List Bool} (h : iter a s = some t) : check (b + a) s = check b t := by
  unfold check
  rw [iter_add h]

theorem check_of {k : Nat} {s t : List Bool} (h : iter k s = some t)
    (hl : hscan fuelR 0 0 (true :: false :: t) = true) : check k s = true := by
  unfold check
  rw [h]
  exact hl

end VisitLaw
