import BB6.SmallEnd
open BB6 BB6.Sym

/-! # The loop entries of the clean-tape tree with the small-end check, as forms (untrusted driver)

Walks `cleanTreeGS Γ d` (`thm/CleanSmallTheorem.lean`) the way the proved explorer `RTree.exploreWE` builds it, and
prints every loop entry (a round start that passes `cleanSmallOK`) with the forms of its three walls a, b, c and its
width W in the class's coordinates, and the class's cone.  One line per entry:

  `E D | a.k a.c… | b.k b.c… | c.k c.c… | W.k W.c… | t.k t.c… ; …`

with D the class's depth in splits (its measure is 2^−D).  No proof reads anything it prints.

usage (after `check_end.sh` has built the shared library):
  lean --load-dynlib=cbuild/so/libBB6all.so --run EntryForms.lean 2199023255552 36 > entries36.txt -/

def ctS : List SMark × YForm × List YForm :=
  let W : YForm := ⟨0, [2, 0]⟩
  ([⟨.M, W.addc (-2)⟩], W, [W])

def fStr (f : YForm) : String := s!"{f.k} " ++ " ".intercalate (f.c.map toString)

def entryLine (ss : List SMark) (sW : YForm) (ts : List YForm) (D : Nat) : Option String :=
  match swwwOf ss with
  | none => none
  | some (a, b, c) =>
    some (s!"E {D} | {fStr a} | {fStr b} | {fStr c} | {fStr sW} | " ++ " ; ".intercalate (ts.map fStr))

partial def walk (Γ : Int) (fuel B : Nat) : Nat → Nat → Nat → Bool → List SMark → YForm → YForm → List YForm → Nat →
    Array String → Array String
  | 0, _, _, _, _, _, _, _, _, acc => acc
  | S + 1, d, nd, moved, ss, sW, w0, ts, D, acc =>
    if (moved && symClean1 ss sW && widerB sW w0 ts Γ) = true then acc else
    if cleanSmallOK Γ ts ss sW w0 = true then
      match entryLine ss sW ts D with
      | some l => acc.push l
      | none => acc
    else
    match symRoundZ ts Γ fuel [] (YForm.const 1) ss sW with
    | some (.newRound ss' sW') => walk Γ fuel B S d nd true ss' sW' w0 ts D acc
    | some _ => acc
    | none =>
      match splitStep ts Γ ss sW with
      | none =>
        match nd, coneMin ts Γ with
        | nd + 1, some z =>
          if dropOK Γ fuel z ss sW w0 ts = true then
            walk Γ fuel B S d nd moved ss sW w0 [dropCone Γ z] D acc
          else acc
        | _, _ => acc
      | some (none, i) =>
        match d with
        | 0 => acc
        | d + 1 =>
          let acc := walk Γ fuel B S d B moved (substL ss i 0) (sW.subst i 0) (w0.subst i 0) (substT ts i 0) (D + 1)
            acc
          walk Γ fuel B S d B moved (substL ss i 1) (sW.subst i 1) (w0.subst i 1) (substT ts i 1) (D + 1) acc
      | some (some (j, s), i) =>
        match d with
        | 0 => acc
        | d + 1 =>
          let ss2 := shearL ss j s; let sW2 := sW.shear j s; let w02 := w0.shear j s; let ts2 := shearT ts j s
          let acc := walk Γ fuel B S d B moved (substL ss2 i 0) (sW2.subst i 0) (w02.subst i 0) (substT ts2 i 0)
            (D + 1) acc
          walk Γ fuel B S d B moved (substL ss2 i 1) (sW2.subst i 1) (w02.subst i 1) (substT ts2 i 1) (D + 1) acc

def main (args : List String) : IO Unit := do
  let Γ := (args.getD 0 "2199023255552").toNat!
  let d := (args.getD 1 "28").toNat!
  let a := walk Γ 1000 4 (10000 + d) d 4 false ctS.1 ctS.2.1 ctS.2.1 ctS.2.2 0 #[]
  IO.println s!"# Γ = {Γ}, d = {d}, entries {a.size}"
  for l in a do IO.println l
