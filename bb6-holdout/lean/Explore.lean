import BB6.SymSplit
open BB6 BB6.Sym

/-! # Building split trees for the endgame (untrusted driver; every verdict is re-checked by `Tree.ok`)

For each even R, the start class of phase-0 pass starts is a = 1 + 2 y₀, b = 2 y₁, E = 2 y₂ (a odd, b even, E even)
with the marks G 1, W a, W b, W c = E − R − 1 and width E; the cone gaps are a, b − a, c − b.  The driver runs rounds;
when a round is undecided it splits a coordinate (the first one whose split decides the round in both children), and
it stops a leaf where the Python checker's classification stops: a close (an end meeting at a constant distance ≤ 2:
here the round is either uncovered or the end meeting is recorded), a break (an end meeting off the predicted chain),
a pass (shapes GWWW, GBW, GMB after the first pass), or leaving phase 0 (round 1 not GBW, round 2 not GMB). -/

instance : Inhabited Tree := ⟨.leaf 0⟩

def shapeOf (ss : List SMark) : String := "G" ++ String.join (ss.map (fun m => match m.t with
  | .G => "G" | .M => "M" | .W => "W" | .B => "B"))

/-- End meetings of one round (distance form, merge?), by stepping the proved event functions. -/
partial def endMeets (ts : List YForm) (Γ : Int) (sL : List SMark) (sg : YForm) (sR : List SMark) (sW : YForm)
    (acc : List (YForm × Bool)) (fuel : Nat) : Option (List (YForm × Bool)) :=
  if fuel = 0 then none else
  let acc := match sR with
    | [m] => if m.t == .M then
        let d := m.p.sub (sg.addc 3)
        acc ++ [(d, d.modDec 4 != some 0)]
      else acc
    | _ => acc
  match symGapEvent ts Γ sL sg sR sW with
  | some (.gap sL' sg' sR' sW') => endMeets ts Γ sL' sg' sR' sW' acc (fuel - 1)
  | some (.pkt sL' sx sR' sW') =>
    match symPktBack ts Γ sL' sx sR' sW' with
    | some (.gap a b c d) => endMeets ts Γ a b c d acc (fuel - 1)
    | some _ => some acc
    | none => none
  | some (.pktM sL' sx sR' sW') =>
    match symPktLand ts Γ sL' sx sR' sW' with
    | some (.gap a b c d) => endMeets ts Γ a b c d acc (fuel - 1)
    | some _ => some acc
    | none => none
  | some _ => some acc
  | none => none

def isConstLe2 (d : YForm) : Bool := match d.constVal with | some v => v ≤ 2 | none => false

def predD (d : YForm) (merge : Bool) : Option YForm :=
  if merge then (d.addc (-2)).half? else (d.half?).map (·.addc 4)

inductive Kind | close | brk | pass | notphase0 | cap
  deriving Repr, BEq

structure Leaf where
  kind : Kind
  rounds : Nat
  deriving Repr

/-- Classify the run of a class: `.inl n` = undecided at round n + 1 (split needed); `.inr leaf`. -/
def classify (ts : List YForm) (Γ : Int) (ss : List SMark) (sW : YForm) (maxR : Nat) : Sum Nat Leaf := Id.run do
  let mut cur := ss
  let mut cw := sW
  let mut hist : List String := []
  let mut last : Option (YForm × Bool) := none
  for rd in [1:maxR + 1] do
    let em := endMeets ts Γ [] (YForm.const 1) cur cw [] 2000
    match symRoundZ ts Γ 1000 [] (YForm.const 1) cur cw with
    | none => return .inl (rd - 1)
    | some (.newRound ss' sW') =>
      let sh := shapeOf ss'
      hist := hist ++ [sh]
      match em with
      | none => return .inl (rd - 1)
      | some ms =>
        for (d, mg) in ms do
          match last with
          | some (ld, lmg) =>
            if d.constVal.isNone then
              match predD ld lmg with
              | some pr => if !(sameForm pr d) then return .inr ⟨.brk, rd⟩
              | none => return .inr ⟨.brk, rd⟩
          | none => pure ()
          last := some (d, mg)
          if isConstLe2 d then return .inr ⟨.close, rd⟩
      if rd == 1 && sh != "GBW" then return .inr ⟨.notphase0, rd⟩
      if rd == 2 && sh != "GMB" then return .inr ⟨.notphase0, rd⟩
      if rd ≥ 4 && hist.drop (hist.length - 3) == ["GWWW", "GBW", "GMB"] then return .inr ⟨.pass, rd⟩
      cur := ss'; cw := sW'
    | some _ => return .inr ⟨.close, rd - 1⟩
  return .inr ⟨.cap, maxR⟩


/-- The first residue test of a round that the class does not decide: the form and the modulus (2 or 4). -/
partial def undecidedResidue (ts : List YForm) (Γ : Int) (sL : List SMark) (sg : YForm) (sR : List SMark) (sW : YForm)
    (fuel : Nat) : Option (YForm × Int) :=
  if fuel = 0 then none else
  let here : Option (YForm × Int) := match sR with
    | m :: _ =>
      if m.t == .M && ltDec m.p (sg.addc 3) ts Γ == some false then
        let d := m.p.sub (sg.addc 3)
        match d.modDec 2 with
        | none => some (d, 2)
        | some 0 => match d.half? with
          | none => some (d, 2)
          | some _ => if (d.modDec 4).isNone then some (d, 4) else none
        | _ => none
      else none
    | [] => none
  match here with
  | some r => some r
  | none =>
    match symGapEvent ts Γ sL sg sR sW with
    | some (.gap a b c d) => undecidedResidue ts Γ a b c d (fuel - 1)
    | some (.pkt sL' sx sR' sW') =>
      match symPktBack ts Γ sL' sx sR' sW' with
      | some (.gap a b c d) => undecidedResidue ts Γ a b c d (fuel - 1)
      | _ => none
    | some (.pktM sL' sx sR' sW') =>
      match symPktLand ts Γ sL' sx sR' sW' with
      | some (.gap a b c d) => undecidedResidue ts Γ a b c d (fuel - 1)
      | _ => none
    | _ => none

/-- The state at the start of round `r + 1`. -/
def stateAt (ts : List YForm) (Γ : Int) (ss : List SMark) (sW : YForm) (r : Nat) : Option (List SMark × YForm) := Id.run do
  let mut cur := ss
  let mut cw := sW
  for _ in [0:r] do
    match symRoundZ ts Γ 1000 [] (YForm.const 1) cur cw with
    | some (.newRound a b) => cur := a; cw := b
    | _ => return none
  return some (cur, cw)

/-- A coordinate whose coefficient in `f` is not divisible by `m`. -/
def splitCoord (f : YForm) (m : Int) : Option Nat :=
  (List.range f.c.length).find? (fun i => f.c.getD i 0 % m != 0)

/-- Build the tree: classify; when undecided, split the first coordinate that lets both children get further. -/
partial def build (k : Nat) (ts : List YForm) (Γ : Int) (ss : List SMark) (sW : YForm) (depth : Nat) (maxR : Nat) :
    Tree × List Leaf :=
  match classify ts Γ ss sW maxR with
  | .inr lf => (.leaf lf.rounds, [lf])
  | .inl r =>
    if depth = 0 then (.leaf r, [⟨.cap, r⟩]) else
    let choice : Option Nat :=
      match stateAt ts Γ ss sW r with
      | some (cur, cw) =>
        match undecidedResidue ts Γ [] (YForm.const 1) cur cw 2000 with
        | some (f, m) => splitCoord f m
        | none => none
      | none => none
    match choice with
    | none => (.leaf r, [⟨.cap, r⟩])
    | some i =>
    let (t0, l0) := build k (substT ts i 0) Γ (substL ss i 0) (sW.subst i 0) (depth - 1) maxR
    let (t1, l1) := build k (substT ts i 1) Γ (substL ss i 1) (sW.subst i 1) (depth - 1) maxR
    (.node i t0 t1, l0 ++ l1)

def startR (R : Int) : List SMark × YForm × List YForm :=
  let a : YForm := ⟨1, [2, 0, 0]⟩
  let b : YForm := ⟨0, [0, 2, 0]⟩
  let E : YForm := ⟨0, [0, 0, 2]⟩
  let c := E.addc (-R - 1)
  ([⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩], E, [a, b.sub a, c.sub b])

def main (args : List String) : IO Unit := do
  let Rmax := (args.getD 0 "64").toNat!
  let Γ : Int := (args.getD 1 "448").toInt!
  let mut total := 0
  let mut allOk := true
  let mut closes : List Nat := []
  let mut counts : List (String × Nat) := []
  let Rs : List Nat := match args.getD 2 "" with
    | "" => (List.range (Rmax / 2)).map (fun r => 2 * (r + 1))
    | lst => (lst.splitOn ",").map String.toNat!
  for Rn in Rs do
    let R : Int := Rn
    let (ss, sW, ts) := startR R
    let (t, leaves) := build 3 ts Γ ss sW 40 24
    let ok := t.ok Γ 1000 3 false ss sW ts
    if !ok then allOk := false; IO.println s!"R={R}: TREE CHECK FAILED"
    total := total + leaves.length
    if leaves.any (·.kind == .close) then closes := closes ++ [Rn]
    if leaves.any (·.kind == .cap) then IO.println s!"R={R}: {(leaves.filter (·.kind == .cap)).length} leaves undecided (cap)"
    for lf in leaves do
      let key := reprStr lf.kind
      counts := match counts.find? (·.1 == key) with
        | some _ => counts.map (fun p => if p.1 == key then (p.1, p.2 + 1) else p)
        | none => counts ++ [(key, 1)]
  IO.println s!"R in list ({Rs.length} values): leaves {total}; every tree checked: {allOk}; Γ = {Γ}"
  IO.println s!"leaf kinds: {counts}"
  IO.println s!"R with a closing leaf: {closes}"
