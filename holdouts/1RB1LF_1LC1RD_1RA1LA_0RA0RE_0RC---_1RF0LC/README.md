# 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC

bbchallenge id 3292. One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LF |
| B | 1LC | 1RD |
| C | 1RA | 1LA |
| D | 0RA | 0RE |
| E | 0RC | --- |
| F | 1RF | 0LC |

## What it does

Family: **Collatz-like (3n/2) with a tower of counters.**

Write `b` for the word `110`. The run is a sequence of *steps*; at the start of each the whole tape is

    W A> 0 b^N 1

a short *wall* `W` (a word ending in 1) on the left and one long block of `N` copies of `b`, blank on both sides.

* **Transfer.** The head builds a junction `111` and sweeps: `L 1 b^(x+2) 111 F> b^(y+1) 1` becomes
  `L 1 b^x 111 F> b^(y+4) 1` in 18y + 50 steps (the head runs to the right end and back, taking two copies of `b`
  from the left block and adding three to the right block). When the left block is used up the right block holds
  about `3N/2` copies and the next step starts. The tape grows on the right during the sweeps: the right side
  grows like sqrt(steps).
* **The wall.** The parity of `N` decides how the step ends; the next step is `W' A> 0 b^N' 1` with
  `N' = (3N + c)/2` and `(W', c)` depending only on `(W, N mod 2)`. The commonest cases:

| wall `W` | `N` even | `N` odd |
|---|---|---|
| `1` | `1`, 3N/2 + 7 | `1^4 b 1`, (3N+9)/2 |
| `1^(3j+1) b 1` (j odd) | `1^(3j+4)`, 3N/2 + 7 | `1 b^(j+1) 1^3 b 1`, (3N+9)/2 |
| `1^(3j+1)` (j even) | `1`, 3N/2 + 7 + j | `1^(3j+4) b 1`, (3N+9)/2 |
| `1 b^k 1^3 b 1` | `1 b^k 1^6`, 3N/2 + 7 | k even: `1 b^(3k/2+2) 1^3 b 1`; k odd: `1^4 b 1 b^((3k-1)/2) 1^3 b 1` |
| `1 b^k 1^6` | k even: `1`, 3N/2 + 3k/2 + 9; k odd: `1^4 b 1`, 3N/2 + (3k+13)/2 | k even: `1^4 b 1`; k odd: `1` |

  So alternating parities lengthen the wall `1^(3j+1)`, an odd step at the wrong moment turns the wall into a
  number `k` (the block `b^k`), and that number is itself multiplied by about 3/2 at later odd steps (with its own
  parity deciding whether a further level appears); two even steps in a row fold the wall back into `N`. The wall
  changes once per step and steps come exponentially further apart: the left side grows like log(steps).

From the run: `N` = 468, 709, 1068, 1609, 2418, 3634, 5462, 8200, 12307, 18465, 27702, ... with walls `1`, `1`,
`1^4 b 1`, `1^7`, `1^10 b 1`, `1^13`, `1`, `1`, `1`, `1^4 b 1`, `1 b^2 1^3 b 1`, ...

**Halting.** The only halting transition is E on 1, reached only through `A> 0 1 1 1` (A writes 1, B and D read the
next two 1s, E the third). No step of the map halts in any case seen:

* the orbit: 40,000 steps of the Lean step map from the step start at step 10,206 of the run (`N` then has 23,405
  bits, 83 walls occur, the map always answers), and 300,000 steps of the plain step map `py/stepmap.py` from
  `1 A> 0 b^468 1` (`N` then has about 175,000 bits; 117 walls occur, the wall `1` in 24% of the steps, the longest
  with three levels such as `1 b^2 1^3 b 1 b^10 1^3 b 1 b^1390 1^3 b 1`);
* the graph: breadth-first search of all walls of at most 300 cells reachable from `1` with either parity
  (279 walls, 558 steps, `py/zonemap.py graph 300`): no halt.

So unlike the Antihydra-type cryptids no halting condition on the map is known. Non-halting is not proved either:
the reachable walls are towers of 3/2-counters whose shapes have not been described in general.

**The step map, for every wall (Lean).** A step is not one transfer loop but three parts:

1. the head crosses the block (`0 C> (110)^k` becomes `(110)^k 0 C>`), builds a few short-lived junctions at the
   right end, and then the junction `L 1 b^x 111 F> b^(y+1) 1` with `x = N - const`;
2. the transfer loop (`sweeps`): `x mod 2` copies are left, the right block has `y + 3 floor(x/2) + 1`;
3. the end of the step works on the wall, crossing the right block a few times (`0110 A> (110)^k` becomes
   `(111)^k 0110 A>`; `(111)^k F> 1` becomes `F> 1 (110)^k`), and leaves `W' A> 0 b^N' 1`.

Parts 1 and 3 are computed by a small simulator (`lean/Zone.lean`, `py/zonemap.py`) that steps cell by cell near
the wall and near the right end, with some copies of `b` kept on each side as working room (about one wall length),
and jumps over the copies between by one of the three shift rules. It never looks at how many copies it jumps, and
gives the step map

    stepMap (W, N) = (W', N')   or halt   or stuck

(`stuck`: `N` too small for the working room (about two copies of `b` per wall cell), a meeting with the block that the rules do not cover, or out of
fuel; never seen along the orbit). Lean proves that the answer is what the machine does, for every wall
(`step_next`, `step_halt`), that blank tape reaches the step start `11101101111101 A> 0 b^48 1` in 10,206 steps
(`blank_to_start`), and the reduction (`halts_iff`): **if the map never answers `stuck` along the orbit from that
step start, the machine halts from blank tape iff the orbit reaches a halting step.** Unconditionally, a halting step
in the orbit gives a halt (`halts_of_orbit`) and an orbit that never ends gives a run that never halts
(`not_halts_of_orbit`).

## Status

Open; reduced to the orbit of the step map. Lean, all by the kernel:

* `lean/Blank.lean` (generated): the halting configurations (`step_none_iff`); no halt in 10,000 steps by the
  kernel, in 10,000,000 by `native_decide`.
* `lean/Rules.lean` (generated by `py/rules.py`): `sweep` (one sweep, any wall), `first` (from the wall `1`, the
  start of a step reaches the first junction, for all `n`).
* `lean/Sweeps.lean`: `one_sweep` and, by induction, `sweeps`: `t` sweeps take the junction `J (x + 2t) y` to
  `J x (y + 3t)` for every wall.
* `lean/Zone.lean` (generic in the machine): the simulator around one long repeated block and its soundness for
  every number of copies (`arun_sound`, `arun_halt`).
* `lean/Reduction.lean`: the three shift rules, `stepMap`, `step_next`, `step_halt`, `blank_to_start`, `orbit`,
  `halts_iff`, `halts_of_orbit`, `not_halts_of_orbit`; `first_steps`: the map answers for the first 40 steps of the
  orbit (kernel evaluation); `orbit_5`: after five steps the wall is `1` and `N = 468`.

Computed: `py/zonemap.py` is the Lean step map in Python: `check 4000` compares it with the plain step map
(`py/stepmap.py`, one step simulated in C by `c/stepc.c`, three values of `N` per case) for 4,000 steps from
`(1, 468)`; `orbit` and `graph` as above. The plain step map agrees with the machine for the ten steps up to step
4.1·10^9 of the run, and ran 300,000 steps from `(1, 468)` without a halt. C (`tools/c/triage.c`): no halt in 10^9
steps.

## For later

* Remove the hypothesis of `halts_iff`: prove that the simulator never answers `stuck` (the head meets the block
  only in the three ways listed, and the buffers of one wall length are enough).
* Describe the walls as a list of counters and prove the step map on that list; then either a halting wall appears
  in the description, or a closed language of walls without `A> 0 111` would prove non-halting. The zone simulator
  gives the exact map to test such a description against; the wall graph up to 300 cells has 279 walls.

## The wall as a stack of counters (observed)

Every wall met along the orbit is `1 X_1 ... X_n` with items `K(k) = b^k 1^3 b 1` (open counter) and
`K'(k) = b^k 1^6` (closed counter), the last item next to the block. `py/stackmodel.py` has a recursive rule for a
step: the parity of N goes into the wall; an open top counter closes (even) or becomes about 3k/2 and passes the
parity of k down (odd); a closed counter is dissolved into the block after passing a parity down, or gets a new open
counter on top (k = 0, odd). The rule gives the same (W', N') as `py/zonemap.py` (the step map proved in Lean) on
100,000 orbit steps (at most 7 items in a wall; N has 58,503 bits at the end) and on 2,563 random walls.
It is fitted, not proved; it has no halting rule; it does not cover a count going below zero, or an empty closed
counter under other items.

    python3 py/stackmodel.py orbit 100000
    python3 py/stackmodel.py random 1500

Tried without success (scratch tools, not in the repository): n-gram closed sets up to n = 30 and pushdown closures
with a DFA on one side; none gives a certificate. About 200,000 random and exhaustive small configurations of the
step-start and mid-step shapes do not halt.

## Remainder classes (family survey)

- **Rounds between end events, by remainder class** (trusted). Sample the run whenever the head is in state B reading 1 with only 0s to its right. Read leftwards from the head, the tape is then `A U^m B`: one long periodic block between two short context words. For each class (A, U, B, m modulo 1 or 2 (the smallest modulus that works for the context)) the next sample is simulated for six values of m and extended as an affine map of m (with a cubic step count). Along the direct run from blank tape to 3·10^9 steps (39 events) the class map predicts the next event in all 26 rounds it applies to. This is an extrapolation checked by computation, not a proof. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC R B 1 check 3e9`
- **273,141 rounds of the class map without a halt** (heuristic). Iterated with exact integers from the event at step 29,839 of the run (A = `(empty)`, U = `110`, m = 79, B = `1^8 0110 1^3`): 273,141 rounds without meeting a halting class; m then has 79,895 bits (about 10^48,102 steps of the machine). 226 distinct contexts occur, the longest of 4,246 cells. The iteration stops there, at a context too large for the six simulations (a second long block has formed); this is a limit of the tool, not an event of the machine. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC R B 1 orbit 273141`
- **No halting class among 530 contexts** (heuristic). Breadth first from the starting context, with every remainder at every context (whether or not the numbers can really produce that sequence of remainders, and only for m large compared with the contexts): 530 contexts expanded, 530 found, to depth 186. None of them halts; the search is not complete (the set of contexts keeps growing), and it says nothing about a halt that needs a context as long as the block itself. 36 contexts longer than 300 cells were not expanded. Command: `python3 holdouts/1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/py/ctxround.py 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC R B 1 bfs 530`

## Pages

- [`pages/holdouts/1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/explainer.html`](../../pages/holdouts/1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/explainer.html)
- [`pages/holdouts/1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/proof-status.html`](../../pages/holdouts/1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/lean/check.sh   # about 1.5 minutes
python3 holdouts/1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/py/zonemap.py check 1500
python3 holdouts/1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/py/zonemap.py orbit 20000   # 1 minute; 40000 takes 15
python3 holdouts/1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/py/zonemap.py graph 80
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1LE_1LC1RC_1LA1RD_1LD0RB_0LC0LF_0LB---`](../1RB1LE_1LC1RC_1LA1RD_1LD0RB_0LC0LF_0LB---/README.md): rename A→C, B→A, C→B, D→E, E→F, F→D and exchange left and right; it is this table started in state B, in a mirror
- [`1RB1LB_1RC1LD_1LA1RE_1RD0LA_0RB0RF_0RA---`](../1RB1LB_1RC1LD_1LA1RE_1RD0LA_0RB0RF_0RA---/README.md): rename A→B, B→C, C→A, D→E, E→F, F→D; it is this table started in state C

<!-- end of related machines -->
