import BB6.Ends
open BB6 BB6.Sym

/-! # Building split trees for the endgame and the exit (untrusted driver; every verdict is re-checked by
`Tree.okEnd`)

For each even R, the endgame's start class of phase-0 pass starts is a = 1 + 2 y₀, b = 2 y₁, E = 2 y₂ (a odd, b even,
E even) with the marks G 1, W a, W b, W c = E − R − 1 and width E; the cone gaps are a, b − a, c − b.  The driver runs
rounds; when a round is undecided it splits a coordinate (the first one whose split decides the round in both
children), and it stops a leaf at the first end event of `BB6/Ends.lean`, with the end meetings of the proved
`symMeetsRounds`: the run left phase 0 (round 1 not G B W, round 2 not G M B), two consecutive end meetings are
decidedly off the chain (`brkDec`), or the round start is a phase-0 pass start with a smaller right end whose next two
rounds are G B W, G M B; or at a close (an end meeting at a constant distance ≤ 2), which only a right end in the
closing set may reach.

The exit's start class is every loop state: a = 1 + 2 y₀, b = 2 y₁, c = 1 + 2 y₂, E = 2 y₃ with the marks W a, W b,
W c (either phase; R = E − c − 1 is free), the cone gaps a, b − a, c − b, E − c.  Its leaves stop at an exit event: a
clean tape (only the end marker, at W − 2), a break of the chain, or a loop state again after 8 rounds (a full pass).

Usage: `ExploreNC Rmax Γ [R,R,…] out` writes one tree per R (lines `R tokens…`; R from 2 to Rmax if no list);
`ExploreNC sym Rlo Γ out` writes one tree for every R ≥ Rlo, with R = 2 y₃ a fourth coordinate; `ExploreNC exit Γ out`
writes the exit tree.  `thm/EndgameTheorem.lean` is generated from `ExploreNC sym 178 448 thm/endgame_sym.txt` and
`ExploreNC 176 448 "" thm/endgame_small.txt` (every even R < 178, the closing set included), `thm/ExitTheorem.lean`
from `ExploreNC exit 390 thm/exit_tree.txt`. -/

instance : Inhabited Tree := ⟨.leaf 0⟩

def shapeOf (ss : List SMark) : String := "G" ++ String.join (ss.map (fun m => match m.t with
  | .G => "G" | .M => "M" | .W => "W" | .B => "B"))

def isConstLe2 (d : YForm) : Bool := match d.constVal with | some v => v ≤ 2 | none => false

/-- The chain's next distance after `d` as a form: `some (some p)`, `some none` (d odd: no successor), or `none` when
d's residue mod 4 is not decided. -/
def predF (d : YForm) : Option (Option YForm) :=
  if d.modDec 4 == some 0 then some ((d.half?).map (·.addc 4))
  else if d.modDec 4 == some 2 then some ((d.addc (-2)).half?)
  else if d.modDec 2 == some 1 then some none
  else none

inductive Kind | close | brk | pass | notphase0 | clean | cap
  deriving Repr, BEq

structure Leaf where
  kind : Kind
  rounds : Nat
  deriving Repr

/-- Where to split when a class is undecided: run `adv` rounds, then split on a residue of the round start after
`at` rounds (`some f m`: or on the residue of the form `f` mod `m`). -/
structure Undec where
  adv : Nat
  atR : Nat
  form : Option (YForm × Int)

/-- The right end of a three-wall round start, when its parities make it a phase-0 pass start: `some (some R′)`,
`some none` (decidedly not), `none` (a parity undecided). -/
def p0R (ss : List SMark) (sW : YForm) : Option (Option YForm) :=
  match swwwOf ss with
  | none => some none
  | some (a, b, c) =>
    match a.modDec 2, b.modDec 2, sW.modDec 2 with
    | some 1, some 0, some 0 => some (some ((sW.sub c).addc (-1)))
    | some _, some _, some _ => some none
    | _, _, _ => none

/-- Classify the run of a class (`sp`: the end events; `sR`: the right end's form, for the endgame). -/
def classify (sp : EndSpec) (ts : List YForm) (Γ : Int) (ss : List SMark) (sW sR : YForm) (maxR : Nat) :
    Sum Undec Leaf := Id.run do
  let mut cur := ss
  let mut cw := sW
  let mut last : Option YForm := none
  for rd in [1:maxR + 1] do
    match symMeetsRounds ts Γ 1000 1 cur cw with
    | none => return .inl ⟨rd - 1, rd - 1, none⟩
    | some ds =>
      for d in ds do
        if isConstLe2 d then return .inr ⟨.close, rd⟩
        if ltDec d (YForm.const 3) ts Γ != some false then return .inr ⟨.cap, rd⟩
        match last with
        | some ld =>
          if brkDec ts Γ ld d then return .inr ⟨.brk, rd⟩
          match predF ld with
          | some (some p) => if !(sameForm p d) then return .inr ⟨.cap, rd⟩
          | some none => return .inr ⟨.cap, rd⟩
          | none => return .inl ⟨rd - 1, rd - 1, some (ld, if (ld.modDec 2).isNone then 2 else 4)⟩
        | none => pure ()
        last := some d
    match symRoundZ ts Γ 1000 [] (YForm.const 1) cur cw with
    | none => return .inl ⟨rd - 1, rd - 1, none⟩
    | some (.newRound ss' sW') =>
      if sp matches .exit then
        if cleanCheck ts Γ ss' sW' then return .inr ⟨.clean, rd⟩
        if rd == 8 then
          match swwwOf ss' with
          | some (a, b, c) =>
            if loopRetCheck 8 ss' sW' then return .inr ⟨.pass, rd⟩
            if [a, b, c, sW'].any (fun f => (f.modDec 2).isNone) then return .inl ⟨rd, rd, none⟩
          | none => pure ()
        cur := ss'; cw := sW'
        continue
      let sh := shapeOf ss'
      if rd == 1 && sh != "GBW" then return .inr ⟨.notphase0, rd⟩
      if rd == 2 && sh != "GMB" then return .inr ⟨.notphase0, rd⟩
      match p0R ss' sW' with
      | none => return .inl ⟨rd, rd, none⟩
      | some (some R') =>
        if ltDec (YForm.const 1) R' ts Γ == some true && ltDec R' sR ts Γ == some true && R'.modDec 2 == some 0 then
          match symRoundZ ts Γ 1000 [] (YForm.const 1) ss' sW' with
          | none => return .inl ⟨rd, rd, none⟩
          | some (.newRound s1 w1) =>
            if shapeOf s1 == "GBW" then
              match symRoundZ ts Γ 1000 [] (YForm.const 1) s1 w1 with
              | none => return .inl ⟨rd, rd + 1, none⟩
              | some (.newRound s2 _) => if shapeOf s2 == "GMB" then return .inr ⟨.pass, rd⟩
              | some _ => pure ()
          | some _ => pure ()
      | some none => pure ()
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


/-- What to split on: the given residue, or the first undecided residue of the round from the state after `atR`
rounds, or an undecided parity of that state (a phase-0 test). -/
def splitChoice (k : Nat) (ts : List YForm) (Γ : Int) (ss : List SMark) (sW : YForm) (u : Undec) : Option (List Nat) :=
  match u.form with
  | some (f, m) => some (oddCoords k f m)
  | none =>
    match stateAt ts Γ ss sW u.atR with
    | some (cur, cw) =>
      match undecidedResidue ts Γ [] (YForm.const 1) cur cw 2000 with
      | some (f, m) => some (oddCoords k f m)
      | none =>
        match swwwOf cur with
        | some (a, b, c) =>
          if (a.modDec 2).isNone then some (oddCoords k a 2)
          else if (b.modDec 2).isNone then some (oddCoords k b 2)
          else if (c.modDec 2).isNone then some (oddCoords k c 2)
          else if (cw.modDec 2).isNone then some (oddCoords k cw 2)
          else none
        | none => none
    | none => none

/-- Build the tree: classify; when undecided, split (after the rounds the class decides). -/
partial def build (sp : EndSpec) (k : Nat) (ts : List YForm) (Γ : Int) (ss : List SMark) (sW sR : YForm)
    (depth maxR : Nat) : Tree × List Leaf :=
  match classify sp ts Γ ss sW sR maxR with
  | .inr lf => (.leaf (if lf.kind == .close then 0 else lf.rounds), [lf])
  | .inl u =>
    if depth = 0 then (.leaf u.adv, [⟨.cap, u.adv⟩]) else
    match splitChoice k ts Γ ss sW u with
    | some (i :: js) =>
      let rec go (js : List Nat) (ss : List SMark) (sW : YForm) (ts : List YForm) (sR : YForm) : Tree × List Leaf :=
        match js with
        | [] =>
          let (t0, l0) := build sp k (substT ts i 0) Γ (substL ss i 0) (sW.subst i 0) (sR.subst i 0) (depth - 1) maxR
          let (t1, l1) := build sp k (substT ts i 1) Γ (substL ss i 1) (sW.subst i 1) (sR.subst i 1) (depth - 1) maxR
          (.node i t0 t1, l0 ++ l1)
        | j :: js =>
          let (t, l) := go js (skewL ss i j 1) (sW.skew i j 1) (skewT ts i j 1) (sR.skew i j 1)
          (.skew i j 1 t, l)
      let (t, l) := go js ss sW ts sR
      (.adv u.adv t, l)
    | _ => (.leaf u.adv, [⟨.cap, u.adv⟩])

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

/-- The start class with R free (R = 2 y₃): cone gaps a, b − a, c − b and R ≥ Rlo. -/
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


/-- The left countdown L₁ = 147 b + 280 E − 392 c − 578 of `startR R`. -/
def startL (R : Int) : YForm :=
  let b : YForm := ⟨0, [0, 2, 0]⟩
  let E : YForm := ⟨0, [0, 0, 2]⟩
  L1Form b (E.addc (-R - 1)) E

/-- The L₁ class a close from R needs (2-adic part), as in `thm/EndgameStart.lean`. -/
def closeClass : Nat → Option (Int × Int)
  | 2 => some (2, 0) | 4 => some (2, 0) | 8 => some (8, 0) | 16 => some (32, 0) | 24 => some (64, 32)
  | 32 => some (64, 0) | 48 => some (128, 0) | 64 => some (128, 0) | 176 => some (128, 0) | _ => none

/-- `sym Rlo Γ out`: one tree for every even R ≥ Rlo, R a fourth coordinate. -/
def mainSym (args : List String) : IO Unit := do
  let Rlo : Int := (args.getD 1 "178").toInt!
  let Γ : Int := (args.getD 2 "448").toInt!
  let (ss, sW, ts) := startSym Γ Rlo
  let sR : YForm := ⟨0, [0, 0, 0, 2]⟩
  let (t, leaves) := build .endgame 4 ts Γ ss sW sR 60 30
  let t := relAdv 0 t
  let ok := t.okEnd Γ 1000 4 none .endgame false ss sW ts sR (YForm.const 0) 0 none
  IO.println s!"R ≥ {Rlo} free: leaves {leaves.length}; tree checked (okEnd): {ok}; Γ = {Γ}"
  IO.println s!"leaf kinds: {countKinds leaves}; most rounds {leaves.foldl (fun m l => max m l.rounds) 0}"
  IO.FS.writeFile (args.getD 3 "endgame_sym.txt") (String.intercalate " " (ser t))

/-- The exit's start class: every loop state, a = 1 + 2 y₀, b = 2 y₁, c = 1 + 2 y₂, E = 2 y₃ (as `thm/ExitStart.lean`). -/
def startExit : List SMark × YForm × List YForm :=
  let a : YForm := ⟨1, [2, 0, 0, 0]⟩
  let b : YForm := ⟨0, [0, 2, 0, 0]⟩
  let c : YForm := ⟨1, [0, 0, 2, 0]⟩
  let E : YForm := ⟨0, [0, 0, 0, 2]⟩
  ([⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩], E, [a, b.sub a, c.sub b, E.sub c])

/-- `exit Γ out`: the exit tree. -/
def mainExit (args : List String) : IO Unit := do
  let Γ : Int := (args.getD 1 "390").toInt!
  let (ss, sW, ts) := startExit
  let (t, leaves) := build .exit 4 ts Γ ss sW (YForm.const 0) 40 16
  let t := relAdv 0 t
  let ok := t.okEnd Γ 1000 4 none .exit false ss sW ts (YForm.const 0) (YForm.const 0) 0 none
  IO.println s!"exit start class: leaves {leaves.length}; tree checked (okEnd): {ok}; Γ = {Γ}"
  IO.println s!"leaf kinds: {countKinds leaves}; most rounds {leaves.foldl (fun m l => max m l.rounds) 0}"
  IO.FS.writeFile (args.getD 2 "exit_tree.txt") (String.intercalate " " (ser t))

def main (args : List String) : IO Unit := do
  if args.getD 0 "" == "sym" then mainSym args else
  if args.getD 0 "" == "exit" then mainExit args else
  let Rmax := (args.getD 0 "64").toNat!
  let Γ : Int := (args.getD 1 "448").toInt!
  let mut total := 0
  let mut serial : List String := []
  let mut counts : List (String × Nat) := []
  let mut closes : List Nat := []
  let mut fails : List Nat := []
  let Rs : List Nat := match args.getD 2 "" with
    | "" => (List.range (Rmax / 2)).map (fun r => 2 * (r + 1))
    | lst => (lst.splitOn ",").map String.toNat!
  for Rn in Rs do
    let R : Int := Rn
    let (ss, sW, ts) := startR R
    let (t, leaves) := build .endgame 3 ts Γ ss sW (YForm.const R) 40 30
    let t := relAdv 0 t
    let ok := t.okEnd Γ 1000 3 (closeClass Rn) .endgame false ss sW ts (YForm.const R) (startL R) 0 none
    if !ok then fails := fails ++ [Rn]
    serial := serial ++ [toString Rn ++ " " ++ String.intercalate " " (ser t)]
    total := total + leaves.length
    if leaves.any (·.kind == .close) then closes := closes ++ [Rn]
    if leaves.any (·.kind == .cap) then IO.println s!"R={R}: {(leaves.filter (·.kind == .cap)).length} leaves undecided (cap)"
    for (k, n) in countKinds leaves do
      counts := match counts.find? (·.1 == k) with
        | some _ => counts.map (fun p => if p.1 == k then (p.1, p.2 + n) else p)
        | none => counts ++ [(k, n)]
  IO.println s!"R in list ({Rs.length} values): leaves {total}; Γ = {Γ}"
  IO.println s!"leaf kinds: {counts}"
  IO.println s!"R with a close leaf (untrusted label): {closes}"
  IO.println s!"R whose tree fails the proved check Tree.okEnd: {fails}"
  IO.FS.writeFile (args.getD 3 "endgame_small.txt") (String.intercalate "\n" serial)
