import BB6.EntryTree
import BB6.RouteEntry
open BB6 BB6.Sym

/-! # The leaves of the route tree with loop entries, dumped (untrusted driver: data for `pieces.py`)

Walks `routeTreeE Γ d` (`../lean/BB6/RouteEntry.lean`) step by step as `RTree.exploreE Γ 1000 (entryOK Γ)` builds it,
from the two-marker start G 1, M m, M E − 2 (m even, E odd), and prints one line per leaf:

  kind D rounds word m0 E0 W marks

`kind` is `clean` (a clean tape: a return to two markers, or the bare one-marker tape), `entry` (a loop entry that
cannot close) or `cut`; the leaf's class has measure 2^D / 2^d of the start class; `word` is the shapes of the round
starts on the path (marks after the gap at 1, joined by `.`); `m0` and `E0` are the start's m and E as forms in the
leaf's coordinates (constant, then the coefficients of y0 and y1), so the class is {(m0(y), E0(y)) : y on the cone};
`W` and `marks` are the leaf's round start in the same coordinates.  `pieces.py` turns them into exact maps of (m, E).

usage (from `../lean`, after `check_route.sh --fast`):
  lean --load-dynlib=cbuild/so/libBB6.so --run ../lock/Pieces.lean 67108864 24 > pieces_24.txt -/

def tchar : MarkT → Char
  | .G => 'G' | .M => 'M' | .W => 'W' | .B => 'B'

def shapeOf (ss : List SMark) : String := String.ofList (ss.map (fun m => tchar m.t))

def formStr (f : YForm) : String := ",".intercalate (toString f.k :: (List.range 2).map (fun i => toString (f.c.getD i 0)))

def leafLine (kind : String) (D r : Nat) (word : List String) (o : List YForm) (ss : List SMark) (sW : YForm) :
    String :=
  let w := ".".intercalate word.reverse
  let ms := ";".intercalate (ss.map (fun m => s!"{tchar m.t}:{formStr m.p}"))
  s!"{kind} {D} {r} {w} {formStr (o.getD 0 (YForm.const 0))} {formStr (o.getD 1 (YForm.const 0))} {formStr sW} {ms}"

/-- The walk; `word` holds the shapes of the round starts so far (newest first), `o` the start's m and E. -/
partial def walkR (Γ : Int) : Nat → Nat → Bool → List SMark → YForm → List YForm → List YForm → Nat → Nat →
    List String → Array String → Array String
  | 0, _, _, ss, sW, _, o, D, r, word, out => out.push (leafLine "cut" D r word o ss sW)
  | S + 1, d, moved, ss, sW, ts, o, D, r, word, out =>
    if (moved && symClean ss sW) = true then out.push (leafLine "clean" D r word o ss sW) else
    if entryOK Γ ts ss sW = true then out.push (leafLine "entry" D r word o ss sW) else
    match symRoundZ ts Γ 1000 [] (YForm.const 1) ss sW with
    | some (.newRound ss' sW') => walkR Γ S d true ss' sW' ts o D (r + 1) (shapeOf ss' :: word) out
    | some _ => out.push (leafLine "cut" D r word o ss sW)
    | none =>
      match d with
      | 0 => out.push (leafLine "cut" D r word o ss sW)
      | d + 1 =>
        match splitStep ts Γ ss sW with
        | none => out.push (leafLine "cut" D r word o ss sW)
        | some (none, i) =>
          if i < 2 then
            let out := walkR Γ S d moved (substL ss i 0) (sW.subst i 0) (substT ts i 0) (substT o i 0) (D - 1) r
              word out
            walkR Γ S d moved (substL ss i 1) (sW.subst i 1) (substT ts i 1) (substT o i 1) (D - 1) r word out
          else out.push (leafLine "cut" D r word o ss sW)
        | some (some (j, s), i) =>
          if i < 2 then
            let ss2 := shearL ss j s; let sW2 := sW.shear j s; let ts2 := shearT ts j s; let o2 := shearT o j s
            let out := walkR Γ S d moved (substL ss2 i 0) (sW2.subst i 0) (substT ts2 i 0) (substT o2 i 0) (D - 1)
              r word out
            walkR Γ S d moved (substL ss2 i 1) (sW2.subst i 1) (substT ts2 i 1) (substT o2 i 1) (D - 1) r word out
          else out.push (leafLine "cut" D r word o ss sW)

def main (args : List String) : IO Unit := do
  let Γ := (args.getD 0 "67108864").toNat!
  let d := (args.getD 1 "24").toNat!
  let m : YForm := ⟨0, [2, 0]⟩
  let E : YForm := ⟨1, [0, 2]⟩
  let out := walkR Γ (10000 + d) d false [⟨.M, m⟩, ⟨.M, E.addc (-2)⟩] E [m, E.sub m] [m, E] d 0 ["MM"] #[]
  IO.println s!"# route tree with loop entries, Γ = {Γ}, d = {d}: {out.size} leaves"
  for l in out do IO.println l
