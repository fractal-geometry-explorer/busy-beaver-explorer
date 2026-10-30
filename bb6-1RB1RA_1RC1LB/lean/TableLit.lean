import Lean
import Cascade
open Lean

namespace BB6b

/-- Parse "dt k v c dt k v c ..." (k = 0 none, 1 add, 2 wave) into the expression of a `List Entry`. -/
def tblExpr (s : String) : Except String Expr := do
  let ws := (s.splitOn " ").filter (· ≠ "") |>.toArray
  if ws.size % 4 != 0 then throw "bad length"
  let nat := mkConst ``Nat
  let ev := mkConst ``Ev
  let evNat := mkApp2 (mkConst ``Prod [0, 0]) ev nat
  let ent := mkApp2 (mkConst ``Prod [0, 0]) nat evNat
  let num (w : String) : Except String Expr := match w.toNat? with
    | some n => pure (mkRawNatLit n)
    | none => throw s!"bad number {w}"
  let n := ws.size / 4
  let mut xs : Array Expr := #[]
  for i in [0:n] do
    let dt ← num ws[4*i]!
    let v ← num ws[4*i+2]!
    let c ← num ws[4*i+3]!
    let evE ← match ws[4*i+1]! with
      | "0" => pure (mkConst ``Ev.none)
      | "1" => pure (mkApp (mkConst ``Ev.add) v)
      | "2" => pure (mkApp (mkConst ``Ev.wave) v)
      | k => throw s!"bad kind {k}"
    xs := xs.push (mkApp4 (mkConst ``Prod.mk [0, 0]) nat evNat dt (mkApp4 (mkConst ``Prod.mk [0, 0]) ev nat evE c))
  -- leaves of at most 256 entries, joined by a balanced tree of appends (the kernel recurses on the depth)
  let mut parts : Array Expr := #[]
  let mut j := 0
  while j < n do
    let mut e := mkApp (mkConst ``List.nil [0]) ent
    for i' in [0:min 256 (n - j)] do
      let i := min n (j + 256) - 1 - i'
      e := mkApp3 (mkConst ``List.cons [0]) ent xs[i]! e
    parts := parts.push e
    j := j + 256
  if parts.isEmpty then return mkApp (mkConst ``List.nil [0]) ent
  while parts.size > 1 do
    let mut next : Array Expr := #[]
    let mut k := 0
    while k < parts.size do
      if k + 1 < parts.size then
        next := next.push (mkApp3 (mkConst ``List.append [0]) ent parts[k]! parts[k+1]!)
      else
        next := next.push parts[k]!
      k := k + 2
    parts := next
  let e := parts[0]!
  return e

open Lean.Elab.Term in
elab "tbl%" s:str : term => do
  match tblExpr s.getString with
  | .ok e => return e
  | .error m => throwError m

end BB6b
