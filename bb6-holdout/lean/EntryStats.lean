import BB6.CleanEntryTree
open BB6 BB6.Sym

/-! # Why the clean-tape tree with loop entries cuts (untrusted driver: statistics only)

Walks the clean-tape tree with loop entries (`cleanTreeGE Γ d`, `thm/CleanEntryTheorem.lean`) the way the proved
explorer `RTree.exploreWE` builds it, and sorts its cut leaves by the first three-wall round start on their path and
the first test of `cleanEntryOK` that it fails there (parities, gaps, width, middle wall, the exclusions after full
passes or after a half pass, or "not decided wider").  No proof reads anything it prints.

usage (after `check_route.sh --fast` has built the shared library):
  lean --load-dynlib=cbuild/so/libBB6.so --run EntryStats.lean 2199023255552 36 -/

def ctS : List SMark × YForm × List YForm :=
  let W : YForm := ⟨0, [2, 0]⟩
  ([⟨.M, W.addc (-2)⟩], W, [W])

/-- Why a three-wall round start fails `cleanEntryOK` (0 = passes). -/
def failReason (Γ : Int) (ts : List YForm) (ss : List SMark) (sW w0 : YForm) : Nat :=
  match swwwOf ss with
  | none => 99
  | some (a, b, c) =>
    let R := (sW.sub c).addc (-1)
    let L := L1Form b c sW
    if !(a.modDec 2 == some 1 && b.modDec 2 == some 0 && sW.modDec 2 == some 0 && R.modDec 2 == some 0) then
      -- parities: is it a loop state (c odd)?
      if c.modDec 2 == some 1 then 1 else 2
    else if !(ltDec (YForm.const 1) R ts Γ == some true) then 3
    else if !(ltDec (YForm.const 447) a ts Γ == some true && ltDec (a.addc 447) b ts Γ == some true &&
        ltDec (b.addc 447) c ts Γ == some true) then 4
    else if !(ltDec (YForm.const (2 ^ 24 - 1)) sW ts Γ == some true) then 5
    else if !(sW.modDec 4 == some 0 || ltDec (b.addc 895) sW ts Γ == some true) then 6
    else if !(exclOK R L ts Γ (exclCert R L ts Γ)) then 7
    else if !(sW.modDec 4 == some 0 ||
      match R.half?, (halfL L sW R).half? with
      | some Rh, some Lh => exclOK Rh Lh ts Γ (exclCert Rh Lh ts Γ)
      | _, _ => false) then 8
    else if !(widerB sW w0 ts Γ) then 9
    else 0

structure Acc3 where
  cuts : Array Nat := Array.replicate 100 0
  mass : Array Nat := Array.replicate 100 0
  threeW : Nat := 0
  -- the number of three-wall starts met on a cut path, histogram
  nmet : Array Nat := Array.replicate 20 0

partial def walk (Γ : Int) (fuel B : Nat) : Nat → Nat → Nat → Bool → List SMark → YForm → YForm → List YForm → Nat →
    Nat → Nat → Acc3 → Acc3
  | 0, _, _, _, _, _, _, _, D, first, met, acc =>
    { acc with cuts := acc.cuts.modify first (· + 1), mass := acc.mass.modify first (· + 2 ^ D),
               nmet := acc.nmet.modify (min met 19) (· + 1) }
  | S + 1, d, nd, moved, ss, sW, w0, ts, D, first, met, acc =>
    if (moved && symClean1 ss sW && widerB sW w0 ts Γ) = true then acc else
    if cleanEntryOK Γ ts ss sW w0 = true then acc else
    let r := failReason Γ ts ss sW w0
    let (first, met) := if r == 99 then (first, met) else (if first == 0 then r else first, met + 1)
    let cut := fun (acc : Acc3) =>
      { acc with cuts := acc.cuts.modify first (· + 1), mass := acc.mass.modify first (· + 2 ^ D),
                 nmet := acc.nmet.modify (min met 19) (· + 1) }
    match symRoundZ ts Γ fuel [] (YForm.const 1) ss sW with
    | some (.newRound ss' sW') => walk Γ fuel B S d nd true ss' sW' w0 ts D first met acc
    | some _ => cut acc
    | none =>
      match splitStep ts Γ ss sW with
      | none =>
        match nd, coneMin ts Γ with
        | nd + 1, some z =>
          if dropOK Γ fuel z ss sW w0 ts = true then
            walk Γ fuel B S d nd moved ss sW w0 [dropCone Γ z] D first met acc
          else cut acc
        | _, _ => cut acc
      | some (none, i) =>
        match d with
        | 0 => cut acc
        | d + 1 =>
          let acc := walk Γ fuel B S d B moved (substL ss i 0) (sW.subst i 0) (w0.subst i 0) (substT ts i 0) (D - 1)
            first met acc
          walk Γ fuel B S d B moved (substL ss i 1) (sW.subst i 1) (w0.subst i 1) (substT ts i 1) (D - 1) first met acc
      | some (some (j, s), i) =>
        match d with
        | 0 => cut acc
        | d + 1 =>
          let ss2 := shearL ss j s; let sW2 := sW.shear j s; let w02 := w0.shear j s; let ts2 := shearT ts j s
          let acc := walk Γ fuel B S d B moved (substL ss2 i 0) (sW2.subst i 0) (w02.subst i 0) (substT ts2 i 0) (D - 1)
            first met acc
          walk Γ fuel B S d B moved (substL ss2 i 1) (sW2.subst i 1) (w02.subst i 1) (substT ts2 i 1) (D - 1) first met
            acc

def main (args : List String) : IO Unit := do
  let Γ := (args.getD 0 "2199023255552").toNat!
  let d := (args.getD 1 "28").toNat!
  let a := walk Γ 1000 4 (10000 + d) d 4 false ctS.1 ctS.2.1 ctS.2.1 ctS.2.2 d 0 0 {}
  IO.println s!"Γ = {Γ}, d = {d}"
  let names := #["no three-wall start", "loop state (c odd)", "other parities", "R < 2", "gap < 448 not decided",
    "width < 2^24 not decided", "middle wall within 896", "full-pass exclusion fails", "half-pass exclusion fails",
    "not decided wider"]
  for i in [0:10] do
    IO.println s!"  {names[i]!}: cut {a.cuts[i]!} (measure {a.mass[i]!}/2^{d})"
  IO.println s!"  three-wall starts met on a cut path: {a.nmet.toList}"
