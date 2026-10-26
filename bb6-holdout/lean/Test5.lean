import BB6.Round
open BB6

instance : BEq St := ⟨fun a b => decide (a = b)⟩

def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616

def genState (seed : Nat) : List Mark × Nat := Id.run do
  let mut s := lcg (seed + 12345)
  let nm := (s / 65536) % 6
  let mut ms : List Mark := []
  let mut q := 4
  let mut u := false
  for _ in [0:nm] do
    s := lcg s
    let t : MarkT := match (s / 65536) % 3 with | 0 => .M | 1 => .W | _ => .B
    s := lcg s
    let base := (s / 65536) % 5
    let len := if u == mval t then 2 * base + 1 else 2 * base
    ms := ms ++ [⟨t, q + len⟩]
    q := q + len + mlen t
    u := mval t
  s := lcg s
  let base := (s / 65536) % 5
  let len := if u == false then 2 * base + 1 else 2 * base
  return (ms, q + len)

def roundStartLike (c : Cfg) : Bool :=
  c.st == .E && c.r 0 == false && c.l 0 == false && c.l 1 == false && c.l 2 == true &&
  (List.range 40).all (fun i => c.l (i + 3) == false)

def normalize (c : Cfg) (nl nr : Nat) : Cfg :=
  let al := (List.range nl).toArray.map c.l
  let ar := (List.range nr).toArray.map c.r
  ⟨fun n => al.getD n false, fun n => ar.getD n false, c.st⟩

/-- Machine: run to the next round start, or report a halt. -/
def nextStart (fuel : Nat) (c : Cfg) (width : Nat) : Option (Option Cfg) := Id.run do
  let mut cur := c
  for i in [0:fuel] do
    match step cur with
    | none => return some none
    | some c' =>
      cur := if i % 64 == 63 then normalize c' width width else c'
      if roundStartLike cur then return some (some cur)
  return none

structure Res where
  rounds : Nat := 0
  listEnd : String := ""
  zipEnd : String := ""
  listWrong : Bool := false
  zipWrong : Bool := false
  zipLonger : Bool := false
  listLonger : Bool := false

/-- Run the machine round by round; each model on its own state, checked against the machine's tape. -/
def tri2 : Nat → Nat → Option MState → Option (List Mark × Nat) → Cfg → Res → Res
  | 0, i, _, _, _, r => { r with rounds := i }
  | n + 1, i, ol, oz, c, r =>
    if ol.isNone && oz.isNone then { r with rounds := i } else
    let W := match ol, oz with | some s, _ => s.W | _, some (_, W) => W | _, _ => 0
    match nextStart 400000 c (W + 64) with
    | none => { r with rounds := i, listEnd := r.listEnd ++ "timeout" }
    | some none =>
      let le := match ol with
        | some s => (match Model.round s with | .halt => "halt" | .uncovered _ => "unc" | _ => "WRONG(next at halt)")
        | none => r.listEnd
      let ze := match oz with
        | some (ms, W) => (match roundZ 1000 [] 1 ms W with | .halt => "halt" | .uncovered => "unc" | _ => "WRONG(next at halt)")
        | none => r.zipEnd
      { r with rounds := i, listEnd := le ++ " (machine halts)", zipEnd := ze ++ " (machine halts)" }
    | some (some c') =>
      let w := (match ol with | some s => s.W | none => 0) + (match oz with | some (_, W) => W | none => 0) + 16
      let mc := cellsOfStart c' w
      let (ol', r) := match ol with
        | none => (none, r)
        | some s => match Model.round s with
          | .next s' => if cellsOfStart (cfgOf s') w == mc then (some s', r) else (none, { r with listWrong := true, listEnd := s!"WRONG at {i}" })
          | .halt => (none, { r with listWrong := true, listEnd := s!"halt claimed at {i}" })
          | .uncovered why => (none, { r with listEnd := s!"unc({why}) at {i}" })
      let (oz', r) := match oz with
        | none => (none, r)
        | some (ms, W) => match roundZ 1000 [] 1 ms W with
          | .newRound ms' W' => if cellsOfStart (roundStart ms' W') w == mc then (some (ms', W'), r)
              else (none, { r with zipWrong := true, zipEnd := s!"WRONG at {i}" })
          | .uncovered => (none, { r with zipEnd := s!"unc at {i}" })
          | _ => (none, { r with zipWrong := true, zipEnd := s!"other at {i}" })
      let r := if ol'.isNone && oz'.isSome then { r with zipLonger := true } else r
      let r := if oz'.isNone && ol'.isSome then { r with listLonger := true } else r
      tri2 n (i + 1) ol' oz' (normalize c' 4 (W + 80)) r

def survey2 (n rounds : Nat) : String := Id.run do
  let mut ok := 0
  let mut lw := 0
  let mut zw := 0
  let mut zl := 0
  let mut ll := 0
  let mut samples : List String := []
  for i in [0:n] do
    let (ms, W) := genState i
    let r := tri2 rounds 0 (some ⟨⟨.G, 1⟩ :: ms, W⟩) (some (ms, W)) (roundStart ms W) {}
    if r.listWrong then lw := lw + 1
    if r.zipWrong then zw := zw + 1
    if r.zipLonger then zl := zl + 1
    if r.listLonger then
      ll := ll + 1
      if samples.length < 8 then samples := samples ++ [s!"list longer: start {repr ms} W={W}: list {r.listEnd}, zipper {r.zipEnd}"]
    if r.listWrong && samples.length < 16 then samples := samples ++ [s!"LIST WRONG: start {repr ms} W={W}: {r.listEnd}"]
    if r.zipWrong && samples.length < 16 then samples := samples ++ [s!"ZIP WRONG: start {repr ms} W={W}: {r.zipEnd}"]
    if !r.listWrong && !r.zipWrong then ok := ok + 1
  return s!"starts {n}: no wrong tape in {ok}; list wrong {lw}; zipper wrong {zw}; zipper covers longer {zl}; list covers longer {ll}\n" ++ String.intercalate "\n" samples

#eval survey2 1500 8
