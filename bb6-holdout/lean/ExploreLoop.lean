import BB6.Loop
open BB6 BB6.Sym

/-! # Building the split tree for pass starts with R free (untrusted driver; the tree is re-checked by `Tree.okLoop`)

The start class: a = 1 + 2 y₀, b = 2 y₁, E = 2 y₂, R = 2 y₃ (so c = E − R − 1), marks G 1, W a, W b, W c, width E.
The cone gaps are a, b − a, c − b and R − 4097 + Γ (so R ≥ 4097); the tree is checked with the proved `Tree.okLoop` before it is written.  A leaf stops at the first round start whose shape
is G W W W with a′ odd, b′ even, E′ even (a *pass leaf*: the run is again at a phase-0 pass start), or where
`ExploreNC` stops (a break of the end chain, leaving phase 0); a close cannot happen this far from the end. -/

instance : Inhabited Tree := ⟨.leaf 0⟩

def shapeOf (ss : List SMark) : String := "G" ++ String.join (ss.map (fun m => match m.t with
  | .G => "G" | .M => "M" | .W => "W" | .B => "B"))

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
  ss : List SMark
  sW : YForm
  deriving Repr

/-- The phase-0 test of a G W W W: `some true` if a′ odd, b′ even, E′ even are decided so, `some false` if one is
decided otherwise or the shape differs, and `.inl (form, 2)` to split when a parity is undecided. -/
def p0Test (ss : List SMark) (sW : YForm) : Sum (YForm × Int) Bool :=
  match ss with
  | [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, _⟩] =>
    match a.modDec 2, b.modDec 2, sW.modDec 2 with
    | some 1, some 0, some 0 => .inr true
    | none, _, _ => .inl (a, 2)
    | _, none, _ => .inl (b, 2)
    | _, _, none => .inl (sW, 2)
    | _, _, _ => .inr false
  | _ => .inr false

/-- `.inl (n, split?)` = undecided at round n + 1 (or at the phase test after round n); `.inr leaf`. -/
def classify (minR : Nat) (mid : Bool) (ts : List YForm) (Γ : Int) (ss : List SMark) (sW : YForm) (maxR : Nat) :
    Sum (Nat × Option (YForm × Int)) Leaf := Id.run do
  let mut cur := ss
  let mut cw := sW
  let mut hist : List String := []
  let mut last : Option (YForm × Bool) := none
  let mut pending : Option Kind := none
  for rd in [1:maxR + 1] do
    let em := endMeets ts Γ [] (YForm.const 1) cur cw [] 2000
    match symRoundZ ts Γ 1000 [] (YForm.const 1) cur cw with
    | none => return .inl (rd - 1, none)
    | some (.newRound ss' sW') =>
      let sh := shapeOf ss'
      hist := hist ++ [sh]
      let mut stop : Option Kind := pending
      match em with
      | none => return .inl (rd - 1, none)
      | some ms =>
        for (d, mg) in ms do
          match last with
          | some (ld, lmg) =>
            if d.constVal.isNone then
              match predD ld lmg with
              | some pr => if !(sameForm pr d) then stop := stop.orElse (fun _ => some .brk)
              | none => stop := stop.orElse (fun _ => some .brk)
          | none => pure ()
          last := some (d, mg)
          if isConstLe2 d then return .inr ⟨.close, rd, ss', sW'⟩
      let prevGBW := (rd == 1 && shapeOf cur == "GBW") || (hist.length ≥ 2 && hist[hist.length - 2]! == "GBW")
      if ((prevGBW && rd > minR) || !mid) && pending.isNone then
        match p0Test ss' sW' with
        | .inl f => return .inl (rd, some f)
        | .inr true => return .inr ⟨.pass, rd, ss', sW'⟩
        | .inr false => pure ()
      if stop.isNone && rd == 1 && sh != "GBW" then stop := some .notphase0
      if stop.isNone && rd == 2 && sh != "GMB" then stop := some .notphase0
      match stop with
      | some k =>
        -- a leaf may not end on a state shaped like a phase-0 pass start: run one more round
        match p0Test ss' sW' with
        | .inl f => return .inl (rd, some f)
        | .inr false => return .inr ⟨k, rd, ss', sW'⟩
        | .inr true => pending := some k
      | none => pure ()
      cur := ss'; cw := sW'
    | some _ => return .inr ⟨.close, rd, cur, cw⟩
  return .inr ⟨.cap, maxR, cur, cw⟩

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

structure LeafX where
  leaf : Leaf
  root : List SMark × YForm   -- the substituted start (for R and L₁ at the root)
  ts : List YForm

partial def build (minR : Nat) (mid : Bool) (ts : List YForm) (Γ : Int) (ss : List SMark) (sW : YForm) (depth : Nat) (maxR : Nat) :
    Tree × List LeafX :=
  match classify minR mid ts Γ ss sW maxR with
  | .inr lf => (.leaf lf.rounds, [⟨lf, (ss, sW), ts⟩])
  | .inl (r, sp) =>
    let cap := (Tree.leaf r, [⟨⟨.cap, r, ss, sW⟩, (ss, sW), ts⟩])
    if depth = 0 then cap else
    let choice : Option (List Nat) :=
      match sp with
      | some (f, m) => some (oddCoords 4 f m)
      | none =>
        match stateAt ts Γ ss sW r with
        | some (cur, cw) =>
          match undecidedResidue ts Γ [] (YForm.const 1) cur cw 2000 with
          | some (f, m) => some (oddCoords 4 f m)
          | none => none
        | none => none
    match choice with
    | some (i :: js) =>
      let rec go (js : List Nat) (ss : List SMark) (sW : YForm) (ts : List YForm) : Tree × List LeafX :=
        match js with
        | [] =>
          let (t0, l0) := build minR mid (substT ts i 0) Γ (substL ss i 0) (sW.subst i 0) (depth - 1) maxR
          let (t1, l1) := build minR mid (substT ts i 1) Γ (substL ss i 1) (sW.subst i 1) (depth - 1) maxR
          (.node i t0 t1, l0 ++ l1)
        | j :: js =>
          let (t, l) := go js (skewL ss i j 1) (sW.skew i j 1) (skewT ts i j 1)
          (.skew i j 1 t, l)
      let (t, l) := go js ss sW ts
      (.adv r t, l)
    | _ => cap

def startFree (Γ : Int) : List SMark × YForm × List YForm :=
  let a : YForm := ⟨1, [2, 0, 0, 0]⟩
  let b : YForm := ⟨0, [0, 2, 0, 0]⟩
  let E : YForm := ⟨0, [0, 0, 2, 0]⟩
  let R : YForm := ⟨0, [0, 0, 0, 2]⟩
  let c := (E.sub R).addc (-1)
  ([⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩], E, [a, b.sub a, c.sub b, R.addc (Γ - 4097)])

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

def rOf (ss : List SMark) (sW : YForm) : YForm :=
  match ss.getLast? with
  | some m => (sW.sub m.p).addc (-1)
  | none => sW
def L1Of (ss : List SMark) (sW : YForm) : YForm :=
  match ss with
  | [⟨_, _⟩, ⟨_, b⟩, ⟨_, c⟩] => ((b.smul 147).add (sW.smul 280)).sub (c.smul 392) |>.addc (-578)
  | _ => YForm.const 0

def showF (f : YForm) : String := s!"{f.k}+{f.c}"

def main (args : List String) : IO Unit := do
  let Γ : Int := (args.getD 0 "448").toInt!
  let depth := (args.getD 1 "40").toNat!
  let (ss, sW, ts) := startFree Γ
  let sR : YForm := ⟨0, [0, 0, 0, 2]⟩
  let sL := match ss with
    | [_, ⟨_, b⟩, ⟨_, c⟩] => L1Form b c sW
    | _ => YForm.const 0
  let mid := args.getD 3 "1" == "1"
  let minR := (args.getD 4 "0").toNat!
  let (t, leaves) := build minR mid ts Γ ss sW depth 24
  let t := relAdv 0 t
  IO.println s!"leaves {leaves.length}"
  let mut counts : List (String × Nat) := []
  for lf in leaves do
    let key := reprStr lf.leaf.kind ++ "/" ++ toString lf.leaf.rounds
    counts := match counts.find? (·.1 == key) with
      | some _ => counts.map (fun p => if p.1 == key then (p.1, p.2 + 1) else p)
      | none => counts ++ [(key, 1)]
  IO.println s!"leaf kinds/rounds: {counts}"
  -- pass leaves: R' and L₁' against the root's R and L₁
  let mut n16 := 0
  let mut n64 := 0
  let mut np := 0
  for lf in leaves do
    if lf.leaf.kind == .pass then
      np := np + 1
      let R0 := rOf lf.root.1 lf.root.2
      let R1 := rOf lf.leaf.ss lf.leaf.sW
      let L0 := L1Of lf.root.1 lf.root.2
      let L1 := L1Of lf.leaf.ss lf.leaf.sW
      if sameForm (R1.smul 16) R0 then n16 := n16 + 1
      else IO.println s!"pass leaf R0={showF R0} R1={showF R1} rounds {lf.leaf.rounds}"
      if sameForm (L1.smul 64) L0 then n64 := n64 + 1
      else IO.println s!"pass leaf L0={showF L0} L1={showF L1}"
  for lf in leaves do
    match stateAt lf.ts Γ lf.root.1 lf.root.2 lf.leaf.rounds with
    | some (e1, e2) =>
      let R0 := rOf lf.root.1 lf.root.2
      let L0 := L1Of lf.root.1 lf.root.2
      if !(notP0Check e1 e2) && !(passCheck lf.ts Γ R0 L0 e1 e2) then
        IO.println s!"leaf fails endCheck: {reprStr lf.leaf.kind} rounds {lf.leaf.rounds} shape {shapeOf e1} R0={showF R0} R1={showF (rOf e1 e2)}"
    | none => IO.println "stateAt failed"
  IO.println s!"pass leaves {np}: 16R'=R in {n16}, 64L1'=L1 in {n64}"
  let ok := t.okLoop Γ 1000 4 false ss sW ts sR sL
  IO.println s!"okLoop: {ok}"
  IO.FS.writeFile (args.getD 2 "loop_tree.txt") (String.intercalate " " (ser t))
