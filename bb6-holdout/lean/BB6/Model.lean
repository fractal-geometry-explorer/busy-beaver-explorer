import BB6.Marks

/-!
# The round recurrence as a function on marks

This is the mark model itself, as a Lean definition: the positions of the marks after one round, computed from
their positions before it, following the rows of the recurrence table ("How the rules give the round recurrence" in
the notes) exactly as the Python and C explorers do.  It is executable: `#eval` runs it, and a configuration can be
compared cell by cell against the machine's own `steps`.  The theorem that the two agree for every round start
that meets the contact conditions is the target of the next layer; here the function is the specification.

The state of a round in progress is the list of marks (sorted by position, the active gap among them), the width
`W`, and which mark is the active gap.  A round ends when the packet reaches the left end, and the next round
starts with every position shifted by 2 (or 4, when a marker sits on cell 0 and becomes the wall `W 5`).
Outcomes: the next round start, a halt (a packet reaching a block), or `uncovered` when a configuration arises that
the proven rules do not cover (marks touching, a packet meeting a marker after a wall or gap, …).
-/

namespace BB6

structure MState where
  marks : List Mark      -- sorted by position, positions distinct
  W : Nat
  deriving Repr

inductive Outcome where
  | next (s : MState)
  | halt
  | uncovered (why : String)
  deriving Repr

namespace Model

/-- Insert keeping the list sorted by position. -/
def insert (m : Mark) : List Mark → List Mark
  | [] => [m]
  | x :: xs => if m.p < x.p then m :: x :: xs else x :: insert m xs

def remove (p : Nat) (ms : List Mark) : List Mark := ms.filter (fun m => m.p != p)

def replace (p : Nat) (m : Mark) (ms : List Mark) : List Mark := insert m (remove p ms)

def firstRight (x : Nat) (ms : List Mark) : Option Mark := ms.find? (fun m => x < m.p)

def lastMark (ms : List Mark) : Option Mark := ms.getLast?

/-- The nearest mark left of `x` that is not a marker (markers are crossed by a packet). -/
def nearestLeftNonM (x : Nat) (ms : List Mark) : Option Mark :=
  (ms.filter (fun m => m.p < x && m.t != .M)).getLast?

/-- The mark immediately left of `m` in the list. -/
def leftNeighbour (m : Mark) (ms : List Mark) : Option Mark :=
  (ms.filter (fun k => k.p < m.p)).getLast?

/-- `k` ends on the cell right before `m` starts: the marks touch. -/
def touches (k m : Mark) : Bool := k.p + mlen k.t == m.p

/-- Result of a packet going left from cell `x`: the new active gap (if any), the marks, or a halt / uncovered case. -/
inductive PR where
  | gap (g : Mark) (ms : List Mark)
  | leftEnd (ms : List Mark)
  | halt
  | uncovered (why : String)

def packetBack (x : Nat) (ms : List Mark) : PR :=
  -- a packet meeting a marker that sits right after a wall or a gap is not covered by the rules
  let bad := ms.any (fun m => m.t == .M && m.p < x &&
    (match leftNeighbour m ms with
     | some k => touches k m && (k.t == .W || k.t == .G)
     | none => false))
  if bad then .uncovered "packet meets marker after a wall or gap" else
  match nearestLeftNonM x ms with
  | none => .leftEnd ms
  | some b =>
    match b.t with
    | .B => .halt
    | .G => let g : Mark := ⟨.G, b.p + 2⟩; .gap g (replace b.p g ms)
    | .W =>
      -- a packet meeting a wall right after a 0-mark is not covered
      let badw := match leftNeighbour b ms with
        | some k => touches k b && mval k.t == false
        | none => false
      if badw then .uncovered "packet meets wall after a 0-mark" else
      let g : Mark := ⟨.G, b.p + 1⟩
      .gap g (insert g (replace b.p ⟨.M, b.p - 1⟩ ms))
    | .M => .uncovered "unreachable"

/-- A shift running right from cell `x` to the next mark (the gap and the wall it met are already removed). -/
def shiftFrom (x : Nat) (ms : List Mark) (W : Nat) : PR × Nat :=
  match firstRight x ms with
  | none => let W' := W + 2; (packetBack (W' - 2) (insert ⟨.M, W' - 2⟩ ms), W')
  | some k =>
    match k.t with
    | .M => let g : Mark := ⟨.G, k.p⟩; (.gap g (replace k.p g ms), W)
    | .W => (packetBack k.p (replace k.p ⟨.B, k.p⟩ ms), W)
    -- As in the Python and C simulators: when the block ends the tape (k.p + 3 = W) this writes a wall in the last two
    -- cells, one past the width — the same tape as no wall and width W − 1, but a later shift that reaches this
    -- "trailing wall" makes it a block past the width, where the machine forms an end marker.  The proved model
    -- `roundZ` (Round.lean) writes the canonical form instead.  Kept here as a faithful port of the simulator.
    | .B => (packetBack (k.p + 2) (replace k.p ⟨.W, k.p + 2⟩ ms), W)
    | .G => (.uncovered "shift meets a sleeping gap", W)

/-- The marks and width at the end of a round, shifted for the next round start. -/
def finish (ms : List Mark) (W : Nat) : MState :=
  let pr : List Mark × Nat :=
    match ms with
    | ⟨.M, 0⟩ :: rest => (⟨.W, 1⟩ :: rest, 4)
    | _ => (ms, 2)
  ⟨⟨.G, 1⟩ :: pr.1.map (fun (m : Mark) => ⟨m.t, m.p + pr.2⟩), W + pr.2⟩

/-- One event of the round: the active gap `g` meets the next mark. -/
def event (g : Mark) (ms : List Mark) (W : Nat) : PR × Nat :=
  -- a gap right after a 0-mark is not covered
  let badg := match leftNeighbour g ms with
    | some k => touches k g && mval k.t == false
    | none => false
  if badg then (.uncovered "gap after a 0-mark", W) else
  match firstRight g.p ms with
  | none =>
    let W' := W + 3
    (packetBack (W' - 2) (insert ⟨.M, W' - 2⟩ (remove g.p ms)), W')
  | some m =>
    match m.t with
    | .M =>
      if m.p < g.p + 3 then (.uncovered "gap overlaps marker", W) else
      let d := m.p - g.p - 3
      if d % 2 == 1 then (.uncovered "odd distance", W) else
      if d % 4 == 0 then
        let g' : Mark := ⟨.G, g.p + d / 2 + 1⟩
        (.gap g' (replace g.p g' (replace m.p ⟨.M, g.p + d / 2 - 1⟩ ms)), W)
      else
        let w : Mark := ⟨.W, g.p + d / 2 + 3⟩
        (packetBack w.p (replace m.p w (remove g.p ms)), W)
    | .W => shiftFrom m.p (remove m.p (remove g.p ms)) W
    | .B => shiftFrom (m.p - 1) (replace m.p ⟨.W, m.p - 1⟩ ms) W      -- the gap stays, asleep
    | .G => (.uncovered "gap meets a sleeping gap", W)

/-- Marks must not overlap or touch in ways the rules exclude: here only the overlap check. -/
def overlapping : List Mark → Bool
  | a :: b :: rest => (b.p < a.p + mlen a.t) || overlapping (b :: rest)
  | _ => false

/-- Run the round: `fuel` bounds the number of events. -/
def run (fuel : Nat) (g : Mark) (ms : List Mark) (W : Nat) : Outcome :=
  match fuel with
  | 0 => .uncovered "out of fuel"
  | fuel + 1 =>
    match event g ms W with
    | (.uncovered why, _) => .uncovered why
    | (.halt, _) => .halt
    | (.leftEnd ms', W') => if overlapping ms' then .uncovered "marks overlap" else .next (finish ms' W')
    | (.gap g' ms', W') => if overlapping ms' then .uncovered "marks overlap" else run fuel g' ms' W'

/-- One round from a round start: the first mark must be the gap at 1. -/
def round (s : MState) : Outcome :=
  match s.marks with
  | ⟨.G, 1⟩ :: _ => run 1000 ⟨.G, 1⟩ s.marks s.W
  | _ => .uncovered "no gap at 1"

/-- `n` rounds. -/
def rounds : Nat → MState → Outcome
  | 0, s => .next s
  | n + 1, s =>
    match round s with
    | .next s' => rounds n s'
    | o => o

end Model

/-! ## Executable comparison with the machine

`cells c n` lists the cells of a configuration from the leftmost one that can be nonzero (we start at the left end
of the tape, which the machine never passes) to cell `n`, for a configuration whose head is on cell `h` — here we
only compare round starts, where the head is on cell 3 and the left stream is `0 0 1 0^∞`. -/

/-- The first `n` cells of a round-start configuration's tape, cell 0 first. -/
def cellsOfStart (c : Cfg) (n : Nat) : List Bool :=
  (List.range n).map (fun i => if i < 3 then c.l (2 - i) else c.r (i - 3))

/-- The tape of a mark state as a round start (head on cell 3). -/
def cfgOf (s : MState) : Cfg :=
  match s.marks with
  | _ :: ms => roundStart ms s.W
  | [] => roundStart [] s.W

end BB6
