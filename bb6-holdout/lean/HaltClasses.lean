import BB6.CloseHalt
import BB6.RouteExplore
open BB6 BB6.Sym

/-! # The classes of pass starts with R ≥ 178 that halt, by scale (untrusted driver, for looking)

The halting pass starts with R ≥ 178 of `thm/PassOpenHalt.lean` halt the same way: the run meets the end at R − 2,
then off the loop's chain at some x, and from there the end meetings halve, x → (x − 2)/2, down to 0, through
three-wall round starts with small right ends, to a close at distance 0, which is a halt (`reach_close_halt`).  On the
route of the full-pass landing at width 13,400 (rounds WWW, BW, MWWM, WWWM, BWM) x = (W − b + 2R + 14)/4, so
W − b = 2^(j+2) − 2R − 22 puts it at 2^j − 2.  Three modes:

* `search mode p rlo rhi K S`: for each even R in [rlo, rhi] and the third gap given by the mode (`pow j`:
  W − b = 2^(j+2) − 2R − 22; `pow3 j`: 3 · 2^(j+2) − 2R − 22; `fix D`: D), follows the class a = 1 + 2y₀, b = 2y₁,
  W = b + D with the symbolic model round by round, splitting it where a round is undecided (at most K splits, at most
  S rounds and splits on a path), to a clean tape or two-marker state (stop), or a round that is not a new round start;
  there the symbolic close run decides whether the class halts, and the classes that do are printed (b as b₀ + [0, 2^k]).
  For `pow j`, K = 1.5 j + 6 and S = 3.5 j + 12 find the class at every j tried (10 to 30).
* `fam W₀ R₀ b₀ k ...`: for each family (as `Fam` in `thm/PassOpenHalt.lean`, first wall free, b ≡ b₀ mod 2^k,
  W − b = W₀ − b₀), whether the close run closes it, and the first N at which `symOpenRun` succeeds (open at every
  depth of `passTreeSym`), if one below 100 does.
* `trace n a b W R`: the model's first n rounds from the pass start with walls at a, b and W − R − 1 and width W: each
  round start's marks as distances from the end, and the round's end meetings.
* `land ap a b W R ...`: for each (a, b, W, R), the pass start a full pass of the loop's chain onto it would come from
  (first wall ap; `../runs/halt_lanes.py` lists the ones on a scale's halting classes), whether the model's eight rounds
  land there, and where the run goes from it.

usage (after `check_end.sh` has built the shared library):
  lean --load-dynlib=cbuild/so/libBB6all.so --run HaltClasses.lean search pow 12 178 198 24 54
  lean --load-dynlib=cbuild/so/libBB6all.so --run HaltClasses.lean fam 840288 178 824282 20
  lean --load-dynlib=cbuild/so/libBB6all.so --run HaltClasses.lean trace 30 449 824282 840288 178
  lean --load-dynlib=cbuild/so/libBB6all.so --run HaltClasses.lean land 449 3187 9698 13400 186 -/

structure SAcc where
  close : Nat := 0
  clean : Nat := 0
  other : Nat := 0
  cut : Nat := 0
  out : Array String := #[]

def fstr (f : YForm) : String := s!"{f.k}+{f.c}"

partial def walk (Γ : Int) (tag : String) : Nat → Nat → List SMark → YForm → List YForm → List YForm → Nat → SAcc →
    SAcc
  | 0, _, _, _, _, _, _, acc => { acc with cut := acc.cut + 1 }
  | S + 1, d, ss, sW, ts, o, r, acc =>
    if (r > 0 && symClean ss sW) = true then { acc with clean := acc.clean + 1 } else
    match symRoundZ ts Γ 1000 [] (YForm.const 1) ss sW with
    | some (.newRound ss' sW') => walk Γ tag S d ss' sW' ts o (r + 1) acc
    | some _ =>
      if symCloseRun ts Γ 100000 [] (YForm.const 1) ss sW then
        { acc with close := acc.close + 1,
                   out := acc.out.push s!"close {tag} a={fstr (o.getD 0 (YForm.const 0))} b={fstr (o.getD 1 (YForm.const 0))} rounds={r} splitsleft={d}" }
      else { acc with other := acc.other + 1 }
    | none =>
      match d with
      | 0 => { acc with cut := acc.cut + 1 }
      | d + 1 =>
        match splitStep ts Γ ss sW with
        | none => { acc with cut := acc.cut + 1 }
        | some (none, i) =>
          let acc := walk Γ tag S d (substL ss i 0) (sW.subst i 0) (substT ts i 0) (substT o i 0) r acc
          walk Γ tag S d (substL ss i 1) (sW.subst i 1) (substT ts i 1) (substT o i 1) r acc
        | some (some (j, s), i) =>
          let ss2 := shearL ss j s; let sW2 := sW.shear j s; let ts2 := shearT ts j s; let o2 := shearT o j s
          let acc := walk Γ tag S d (substL ss2 i 0) (sW2.subst i 0) (substT ts2 i 0) (substT o2 i 0) r acc
          walk Γ tag S d (substL ss2 i 1) (sW2.subst i 1) (substT ts2 i 1) (substT o2 i 1) r acc

def runOne (R D K S : Nat) (tag : String) (acc : SAcc) : SAcc :=
  let a : YForm := ⟨1, [2, 0]⟩
  let b : YForm := ⟨0, [0, 2]⟩
  let W := b.addc (D : Int)
  let c := W.addc (-(R : Int) - 1)
  walk 448 tag S K [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] W [a, b.sub a] [a, b] 0 acc

def search (args : List String) : IO Unit := do
  let mode := args.getD 0 "pow"
  let p := (args.getD 1 "10").toNat!
  let rlo := (args.getD 2 "178").toNat!
  let rhi := (args.getD 3 "198").toNat!
  let K := (args.getD 4 "21").toNat!
  let S := (args.getD 5 "47").toNat!
  let mut acc : SAcc := {}
  let mut R := rlo
  let mut n := 0
  while R ≤ rhi do
    let D? : Option Nat :=
      if mode == "pow" then (if 3 * R + 471 ≤ 2 ^ (p + 2) then some (2 ^ (p + 2) - 2 * R - 22) else none)
      else if mode == "pow3" then (if 3 * R + 471 ≤ 3 * 2 ^ (p + 2) then some (3 * 2 ^ (p + 2) - 2 * R - 22) else none)
      else (if R + 449 ≤ p then some p else none)
    match D? with
    | some D =>
      acc := runOne R D K S s!"R={R} D={D}" { acc with out := #[] }
      n := n + 1
      for l in acc.out do IO.println l
    | none => pure ()
    R := R + 2
  IO.println s!"{mode} {p} R in [{rlo},{rhi}] ({n} values), K={K}: close {acc.close} clean {acc.clean} other {acc.other} cut {acc.cut}"

def typesMayCheckpoint (r : Nat) : List MarkT → Bool
  | [.W, .W, .W] => r == 2 || r == 7 || r == 8
  | [.M] => true
  | _ => false

def symMayCheckpoint (r : Nat) : SPR → Bool
  | .newRound ss _ => typesMayCheckpoint r (ss.map (·.t))
  | _ => true

/-- As `symOpenRun` in `thm/PassOpenHalt.lean`. -/
def openRun (ts : List YForm) (Γ : Int) (N : Nat) (ss : List SMark) (sW : YForm) : Bool :=
  (List.range N).all (fun r => match symRoundsZ ts Γ 1000 r ss sW with
    | some sr => !symMayCheckpoint r sr
    | none => false) &&
  match symRoundsZ ts Γ 1000 N ss sW with
  | some .uncovered => true
  | _ => false

/-- As `Fam.start` in `thm/PassOpenHalt.lean`. -/
def famOf (W0 R0 b0 k : Nat) : List SMark × YForm × List YForm :=
  let a : YForm := ⟨1, [2, 0]⟩
  let b : YForm := ⟨b0, [0, 2 ^ k]⟩
  let W : YForm := ⟨W0, [0, 2 ^ k]⟩
  ([⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W.addc (-(R0 : Int) - 1)⟩], W, [a, b.sub a])

def fam (args : List Nat) : IO Unit := do
  let rec loop : List Nat → IO Unit
    | W0 :: R0 :: b0 :: k :: more => do
      let f := famOf W0 R0 b0 k
      let c := symCloseRun f.2.2 448 3000 [] (YForm.const 1) f.1 f.2.1
      let N := (List.range 100).find? (fun N => openRun f.2.2 448 N f.1 f.2.1)
      IO.println s!"W0={W0} R0={R0} b0={b0} k={k}: closes {c}; open run: {N}"
      loop more
    | _ => pure ()
  loop args

def tc : MarkT → String | .W => "W" | .M => "M" | .B => "B" | .G => "G"

partial def trace (ms : List Mark) (W n : Nat) : IO Unit := do
  if n == 0 then return
  let ds := meetsRounds 100000 1 ms W
  let s := " ".intercalate (ms.map (fun m => s!"{tc m.t}{(W : Int) - (m.p : Int)}"))
  IO.println s!"W={W} {s}  meets={ds}"
  match roundZ 100000 [] 1 ms W with
  | .newRound ms' W' => trace ms' W' (n - 1)
  | .uncovered => IO.println "uncovered"
  | _ => IO.println "other"

/-- From a pass start, the model's rounds to a clean tape wider than `W0` or a round it does not cover (then the close
run says whether it closes). -/
partial def runTo (ms : List Mark) (W n W0 : Nat) : String :=
  if n == 0 then "out of rounds" else
  match roundZ 1000000 [] 1 ms W with
  | .newRound ms' W' =>
    if (match ms' with | [⟨.M, p⟩] => p + 2 == W' | _ => false) && W' > W0 then s!"clean tape {W'}"
    else runTo ms' W' (n - 1) W0
  | .uncovered => if closeRun 1000000 ⟨[], 1, ms, W⟩ then s!"close at width {W}" else s!"uncovered, no close, width {W}"
  | .halt => "halt"
  | _ => "other"

/-- For each landing (a₁, b₁, W₁, R₁): the pass start a full pass would come from (first wall `ap`, middle wall
64b₁ − 48W₁ + 128R₁ − 98, width W₁ − 24, right end 16R₁), whether its gaps are at least 448, whether the model's eight
rounds from it land exactly there with every end meeting at least 3, and where the run goes from the landing. -/
def land (ap : Nat) : List Nat → IO Unit
  | a1 :: b1 :: W1 :: R1 :: more => do
    let E := W1 - 24
    let R0 := 16 * R1
    let bpI : Int := 64 * (b1 : Int) - 48 * (W1 : Int) + 128 * (R1 : Int) - 98
    let bp := bpI.toNat
    let cp := E - R0 - 1
    let ok := bpI ≥ (ap : Int) + 448 && bp + 448 ≤ cp && ap % 2 == 1 && bp % 2 == 0
    let st := [⟨.W, ap⟩, ⟨.W, bp⟩, ⟨.W, cp⟩]
    let minD := (meetsRounds 1000000 8 st E).foldl min 1000000000
    let landed := match roundsZ 1000000 8 st E with
      | .newRound [⟨.W, x⟩, ⟨.W, y⟩, ⟨.W, z⟩] W' => x == a1 && y == b1 && z == W1 - R1 - 1 && W' == W1
      | _ => false
    let rest := if landed then runTo [⟨.W, a1⟩, ⟨.W, b1⟩, ⟨.W, W1 - R1 - 1⟩] W1 400 W1 else "-"
    IO.println s!"landing a={a1} b={b1} W={W1} R={R1}: from a={ap} b={bp} c={cp} W={E} R={R0}, gaps ok {ok}, lands {landed} (least end meeting {minD}); then {rest}"
    land ap more
  | _ => pure ()

def main (args : List String) : IO Unit := do
  match args with
  | "search" :: rest => search rest
  | "fam" :: rest => fam (rest.map String.toNat!)
  | ["trace", n, a, b, W, R] =>
    let (a, b, W, R) := (a.toNat!, b.toNat!, W.toNat!, R.toNat!)
    trace [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W n.toNat!
  | "land" :: ap :: rest => land ap.toNat! (rest.map String.toNat!)
  | _ => IO.println "usage: search pow|pow3|fix p rlo rhi K S | fam W0 R0 b0 k ... | trace n a b W R | land ap a b W R ..."
