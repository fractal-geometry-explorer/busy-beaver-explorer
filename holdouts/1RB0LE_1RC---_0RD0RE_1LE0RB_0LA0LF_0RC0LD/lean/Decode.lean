import Pieces

/-!
# Reading the certificate

The classes and the list `pre` are stored as strings of numbers (`py/replay/gen.py` writes them) and read back here.
The reading is not trusted: the theorems are about whatever lists come out.
-/

namespace H100726

/-- The numbers of a string of decimal numbers separated by anything else (in reverse order of reading). -/
def numsRev : List Char → Nat → Bool → List Nat → List Nat
  | [], n, b, acc => if b then n :: acc else acc
  | ch :: t, n, b, acc =>
    if ch.isDigit then numsRev t (10 * n + (ch.toNat - '0'.toNat)) true acc
    else numsRev t 0 false (if b then n :: acc else acc)

def numsOf (s : String) : List Nat := (numsRev s.toList 0 false []).reverse

def dNat : List Nat → Option (Nat × List Nat)
  | n :: r => some (n, r)
  | [] => none

def dList {α : Type} (f : List Nat → Option (α × List Nat)) : Nat → List Nat → Option (List α × List Nat)
  | 0, r => some ([], r)
  | k + 1, r =>
    match f r with
    | some (x, r') =>
      match dList f k r' with
      | some (xs, r'') => some (x :: xs, r'')
      | none => none
    | none => none

/-- A count: `c`, the number of coefficients, the coefficients. -/
def dCnt (r : List Nat) : Option (Cnt × List Nat) :=
  match r with
  | c :: n :: r =>
    match dList dNat n r with
    | some (a, r') => some (⟨c, a⟩, r')
    | none => none
  | _ => none

/-- A segment: 0 (cells) or 1 (block), the length of the word, its bits. -/
def dSeg (r : List Nat) : Option (Seg × List Nat) :=
  match r with
  | k :: n :: r =>
    match dList dNat n r with
    | some (w, r') => some ((if k = 0 then Seg.cells else Seg.blk) (w.map (· == 1)), r')
    | none => none
  | _ => none

mutual
/-- A tree in preorder: `0 K` (halting leaf), `1 K j n counts` (leaf to a node), `2 v d k children` (residues),
`3 v t k children` (first values), `4 u w child child` (comparison). -/
def dTree : Nat → List Nat → Option (STree Leaf × List Nat)
  | 0, _ => none
  | f + 1, r =>
    match r with
    | 0 :: K :: r => some (.leaf (.halt K), r)
    | 1 :: K :: j :: n :: r =>
      match dList dCnt n r with
      | some (cs, r') => some (.leaf (.node K j cs), r')
      | none => none
    | 2 :: v :: d :: k :: r =>
      match dTrees f k r with
      | some (ch, r') => some (.node (.res v d) ch, r')
      | none => none
    | 3 :: v :: t :: k :: r =>
      match dTrees f k r with
      | some (ch, r') => some (.node (.peel v t) ch, r')
      | none => none
    | 4 :: u :: w :: r =>
      match dTrees f 2 r with
      | some (ch, r') => some (.node (.cmp u w) ch, r')
      | none => none
    | _ => none

def dTrees : Nat → Nat → List Nat → Option (List (STree Leaf) × List Nat)
  | 0, _, _ => none
  | _ + 1, 0, r => some ([], r)
  | f + 1, k + 1, r =>
    match dTree f r with
    | some (t, r') =>
      match dTrees f k r' with
      | some (ts, r'') => some (t :: ts, r'')
      | none => none
    | none => none
end

def fuel : Nat := 1000000

/-- A class: isH, the residues, the segments, the tree. -/
def dCls (r : List Nat) : Option (Cls × List Nat) :=
  match r with
  | h :: n :: r =>
    match dList dNat n r with
    | some (res, r1) =>
      match r1 with
      | m :: r1 =>
        match dList dSeg m r1 with
        | some (text, r2) =>
          match dTree fuel r2 with
          | some (t, r3) => some (⟨text, res, h == 1, t⟩, r3)
          | none => none
        | none => none
      | [] => none
    | none => none
  | _ => none

/-- An entry of `pre`: the segments, the counts, K, j, the counts at the end. -/
def dPre (r : List Nat) : Option (PreE × List Nat) :=
  match r with
  | m :: r =>
    match dList dSeg m r with
    | some (text, r1) =>
      match r1 with
      | n :: r1 =>
        match dList dCnt n r1 with
        | some (cs, r2) =>
          match r2 with
          | K :: j :: n' :: r2 =>
            match dList dCnt n' r2 with
            | some (tcs, r3) => some (⟨text, cs, K, j, tcs⟩, r3)
            | none => none
          | _ => none
        | none => none
      | [] => none
    | none => none
  | [] => none

/-- All records of a string (as many as it holds). -/
def dAll {α : Type} (f : List Nat → Option (α × List Nat)) : Nat → List Nat → List α
  | 0, _ => []
  | _ + 1, [] => []
  | k + 1, r =>
    match f r with
    | some (x, r') => x :: dAll f k r'
    | none => []

def readCls (s : String) : List Cls := dAll dCls fuel (numsOf s)
def readPre (s : String) : List PreE := dAll dPre fuel (numsOf s)

end H100726
