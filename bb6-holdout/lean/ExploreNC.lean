import BB6.Meets
open BB6 BB6.Sym

/-! # Building split trees for the endgame (untrusted driver; every verdict is re-checked by `Tree.ok`)

For each even R, the start class of phase-0 pass starts is a = 1 + 2 y₀, b = 2 y₁, E = 2 y₂ (a odd, b even, E even)
with the marks G 1, W a, W b, W c = E − R − 1 and width E; the cone gaps are a, b − a, c − b.  The driver runs rounds;
when a round is undecided it splits a coordinate (the first one whose split decides the round in both children), and
it stops a leaf where the Python checker's classification stops: a close (an end meeting at a constant distance ≤ 2:
here the round is either uncovered or the end meeting is recorded), a break (an end meeting off the predicted chain),
a pass (shapes GWWW, GBW, GMB after the first pass), or leaving phase 0 (round 1 not GBW, round 2 not GMB).

Usage: `ExploreNC Rmax Γ [R,R,…] out` writes one tree per R (lines `R tokens…`); `ExploreNC sym Rlo Γ out` writes one
tree for every R ≥ Rlo, with R = 2 y₃ a fourth coordinate.  `thm/EndgameTheorem.lean` is generated from
`ExploreNC sym 178 448 thm/endgame_sym.txt` and `ExploreNC 0 448 6,10,12,…,174 thm/endgame_small.txt` (the even R < 178
outside the closing set). -/

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
    | some _ => return .inr ⟨.close, rd⟩
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

/-- The coordinates whose coefficient in `f` is not divisible by `m`: the first is split, the others are first skewed
onto it (yᵢ = zᵢ + zⱼ makes cⱼ + cᵢ divisible by m), so one split decides the residue. -/
def oddCoords (k : Nat) (f : YForm) (m : Int) : List Nat :=
  (List.range k).filter (fun i => f.c.getD i 0 % m != 0)

/-- Build the tree: classify; when undecided, split the first coordinate that lets both children get further. -/
partial def build (k : Nat) (ts : List YForm) (Γ : Int) (ss : List SMark) (sW : YForm) (depth : Nat) (maxR : Nat) :
    Tree × List Leaf :=
  match classify ts Γ ss sW maxR with
  | .inr lf => (.leaf lf.rounds, [lf])
  | .inl r =>
    if depth = 0 then (.leaf r, [⟨.cap, r⟩]) else
    let choice : Option (List Nat) :=
      match stateAt ts Γ ss sW r with
      | some (cur, cw) =>
        match undecidedResidue ts Γ [] (YForm.const 1) cur cw 2000 with
        | some (f, m) => some (oddCoords k f m)
        | none => none
      | none => none
    match choice with
    | some (i :: js) =>
      let rec go (js : List Nat) (ss : List SMark) (sW : YForm) (ts : List YForm) : Tree × List Leaf :=
        match js with
        | [] =>
          let (t0, l0) := build k (substT ts i 0) Γ (substL ss i 0) (sW.subst i 0) (depth - 1) maxR
          let (t1, l1) := build k (substT ts i 1) Γ (substL ss i 1) (sW.subst i 1) (depth - 1) maxR
          (.node i t0 t1, l0 ++ l1)
        | j :: js =>
          let (t, l) := go js (skewL ss i j 1) (sW.skew i j 1) (skewT ts i j 1)
          (.skew i j 1 t, l)
      let (t, l) := go js ss sW ts
      (.adv r t, l)
    | _ => (.leaf r, [⟨.cap, r⟩])

def startR (R : Int) : List SMark × YForm × List YForm :=
  let a : YForm := ⟨1, [2, 0, 0]⟩
  let b : YForm := ⟨0, [0, 2, 0]⟩
  let E : YForm := ⟨0, [0, 0, 2]⟩
  let c := E.addc (-R - 1)
  ([⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩], E, [a, b.sub a, c.sub b])

def ser : Tree → List String
  | .leaf n => ["L" ++ toString n]
  | .node i a b => ("N" ++ toString i) :: (ser a ++ ser b)
  | .skew i j s t => ("S" ++ toString i ++ "," ++ toString j ++ "," ++ toString s) :: ser t
  | .adv n t => ("A" ++ toString n) :: ser t

/-- `build` records at each split the absolute round it happens at (`adv r`, rounds from the root) and at each leaf
its absolute number of rounds; the checked tree runs each stretch once: rounds relative to the last advance. -/
def relAdv (rp : Nat) : Tree → Tree
  | .leaf n => .leaf (n - rp)
  | .adv r t => if rp < r then .adv (r - rp) (relAdv r t) else relAdv rp t
  | .node i a b => .node i (relAdv rp a) (relAdv rp b)
  | .skew i j s t => .skew i j s (relAdv rp t)

/-- The start class with R free (R = 2 y₃, as in `ExploreLoop`): cone gaps a, b − a, c − b and R ≥ Rlo. -/
def startSym (Γ Rlo : Int) : List SMark × YForm × List YForm :=
  let a : YForm := ⟨1, [2, 0, 0, 0]⟩
  let b : YForm := ⟨0, [0, 2, 0, 0]⟩
  let E : YForm := ⟨0, [0, 0, 2, 0]⟩
  let R : YForm := ⟨0, [0, 0, 0, 2]⟩
  let c := (E.sub R).addc (-1)
  ([⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩], E, [a, b.sub a, c.sub b, R.addc (Γ - Rlo)])

def countKinds (leaves : List Leaf) : List (String × Nat) := Id.run do
  let mut counts : List (String × Nat) := []
  for lf in leaves do
    let key := reprStr lf.kind
    counts := match counts.find? (·.1 == key) with
      | some _ => counts.map (fun p => if p.1 == key then (p.1, p.2 + 1) else p)
      | none => counts ++ [(key, 1)]
  return counts

/-- The leaves of a tree whose own check fails, with the form of R there (untrusted diagnostics). -/
partial def failingLeaves (Γ : Int) (k : Nat) : Tree → Bool → List SMark → YForm → List YForm → YForm →
    List (Nat × String)
  | .leaf n, wf, ss, sW, ts, sR =>
    if (Tree.leaf n).okNC Γ 1000 k wf ss sW ts then [] else [(n, s!"R = {sR.k} + {sR.c}")]
  | .adv n t, wf, ss, sW, ts, sR =>
    if !(Tree.adv n (.leaf 0)).okNC Γ 1000 k wf ss sW ts then [(n, s!"adv fails; R = {sR.k} + {sR.c}")] else
    match symRoundsZ ts Γ 1000 n ss sW with
    | some (.newRound ss' sW') => failingLeaves Γ k t true ss' sW' ts sR
    | _ => [(n, "adv rounds fail")]
  | .node i t0 t1, wf, ss, sW, ts, sR =>
    failingLeaves Γ k t0 wf (substL ss i 0) (sW.subst i 0) (substT ts i 0) (sR.subst i 0) ++
      failingLeaves Γ k t1 wf (substL ss i 1) (sW.subst i 1) (substT ts i 1) (sR.subst i 1)
  | .skew i j s t, wf, ss, sW, ts, sR =>
    failingLeaves Γ k t wf (skewL ss i j s) (sW.skew i j s) (skewT ts i j s) (sR.skew i j s)

/-- `sym Rlo Γ out`: one tree for every even R ≥ Rlo, R a fourth coordinate. -/
def mainSym (args : List String) : IO Unit := do
  let Rlo : Int := (args.getD 1 "178").toInt!
  let Γ : Int := (args.getD 2 "448").toInt!
  let (ss, sW, ts) := startSym Γ Rlo
  let (t, leaves) := build 4 ts Γ ss sW 60 24
  let t := relAdv 0 t
  let ok := t.ok Γ 1000 4 false ss sW ts
  let nc := t.okNC Γ 1000 4 false ss sW ts
  IO.println s!"R ≥ {Rlo} free: leaves {leaves.length}; tree checked: {ok}; no close: {nc}; Γ = {Γ}"
  IO.println s!"leaf kinds: {countKinds leaves}"
  for (n, d) in failingLeaves Γ 4 t false ss sW ts ⟨0, [0, 0, 0, 2]⟩ do
    IO.println s!"  failing leaf ({n} rounds): {d}"
  IO.FS.writeFile (args.getD 3 "endgame_sym.txt") (String.intercalate " " (ser t))

def main (args : List String) : IO Unit := do
  if args.getD 0 "" == "sym" then mainSym args else
  let Rmax := (args.getD 0 "64").toNat!
  let Γ : Int := (args.getD 1 "448").toInt!
  let mut total := 0
  let mut allOk := true
  let mut closes : List Nat := []
  let mut ncFail : List Nat := []
  let mut serial : List String := []
  let mut counts : List (String × Nat) := []
  let Rs : List Nat := match args.getD 2 "" with
    | "" => (List.range (Rmax / 2)).map (fun r => 2 * (r + 1))
    | lst => (lst.splitOn ",").map String.toNat!
  for Rn in Rs do
    let R : Int := Rn
    let (ss, sW, ts) := startR R
    let (t, leaves) := build 3 ts Γ ss sW 40 24
    let t := relAdv 0 t
    let ok := t.ok Γ 1000 3 false ss sW ts
    if !ok then allOk := false; IO.println s!"R={R}: TREE CHECK FAILED"
    let nc := t.okNC Γ 1000 3 false ss sW ts
    if !nc then ncFail := ncFail ++ [Rn]
    serial := serial ++ [toString Rn ++ " " ++ String.intercalate " " (ser t)]

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
  IO.println s!"R with a closing leaf (untrusted label): {closes}"
  IO.println s!"R whose tree fails the proved no-close check: {ncFail}"
  IO.FS.writeFile (args.getD 3 "endgame_trees.txt") (String.intercalate "\n" serial)

