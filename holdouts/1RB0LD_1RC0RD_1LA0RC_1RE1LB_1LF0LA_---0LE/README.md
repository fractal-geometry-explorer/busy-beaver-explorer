# 1RB0LD_1RC0RD_1LA0RC_1RE1LB_1LF0LA_---0LE

bbchallenge id 64598, a six-state holdout of group G05 (growth class sqrt/fixed: the left side grows). **Open.**
Each lap copies the tape 5 cells further left; all change happens in an irregular zone of about 900 cells at the
right end, where the lap turns.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 1RC | 0RD |
| C | 1LA | 0RC |
| D | 1RE | 1LB |
| E | 1LF | 0LA |
| F | --- | 0LE |

## Status

**Open.** Lean, kernel (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps; in
10,000,000 by `native_decide`. Lean, kernel, for every length and every surrounding tape:
- `lean/Passes.lean`: the shift rules `sweep_right` and `sweep_left_A`;
- `lean/RightPass.lean`: the right sweep as a 4-state transducer on tokens (`rule_sound`, ten crossings), and
  `pass_sound`, the sweep over any token list the transducer accepts, by induction on the list;
- `lean/LeftPass.lean`: the left sweep's crossings of a block `1^(2k) 0` from two of its three states, for every k,
  with the next state given by k mod 3.

C (`tools/c/triage.c`): no halt in 10^9 steps; `c/laps.c`: none in 2·10^9.

**The 115-119 wall-carry signature is an artefact here** (25-26 November 2026). The screen in
`holdouts/recent-proofs/recursive-sweeps-nov23-25.md` flagged this machine because, near the left end, the first
segment entry takes the values {2, 5, 8} (or {0, 3, 6}, {1, 4, 7}) behind the fixed word `7 7 1 1 2`. Each value
occurs exactly once per lap (2,910 times each in 3·10^7 steps), because each lap copies the whole tape left of the
turning point unchanged (below). The values are the steps of one leftward zigzag through a `1^8` block, 3 cells at a
time. They are not a carry coming back from the far end. The busycoq #115 proof does not transfer as it stands.

## What it does

All of this is measured on the run (`c/`), except where a Lean file is named.

- **Laps.** A lap runs from the left end to a turning point inside the tape and back. The left end moves 5 cells
  left per lap. The turning point does not follow it: in absolute position it stays between -659 and +228 (2·10^9
  steps, 8,281 laps), so laps get longer and the left side grows like the square root of the step count.
- **Each lap copies the tape.** Read from its own left end, the tape after a lap equals the tape before it except
  within the last 5 to 469 cells before the turning point (median 32, over 2,614 laps to 2·10^8 steps,
  `c/copycheck.c`). So everything left of the turning point is an inert record (the *body*), moved 5 cells left
  per lap, and all the change happens in a zone at the right end, fixed in absolute position.
- **Tokens.** At the start of a lap the tape is a word over `x = 1 0`, `y = 1 1 0`, `u = 1 0 0`, `v = 1 1 0 0`.
- **Right sweep** (`lean/RightPass.lean`). Going right, the head crosses one token at a time. Between tokens it is
  in one of four scanner states, a machine state with a fixed word on its left: `D0` (D, `1 0 1 0`), `D1` (D,
  `1 1 1 0`), `E` (E, `1 0 1 0 1`), `C` (C, `1 1 1 0`). From D, `x` and `y` keep D and `v` gives E; from E, `x` keeps
  E and `y` gives `D1`; from C, `x` gives `D0` and `u` gives E. Behind it the head leaves blocks `1^(2k) 0`
  (k = 1 to 6 in the run). The run never shows D on `u`, E on `v`, or C on `y` or `v`.
- **Left sweep** (`lean/LeftPass.lean`). Going left, the head reads the blocks back and writes tokens again. It has
  three states, `L0` (D), `L1` (A), `L2` (B), standing on the `0` at a block's end. From `L0` a block `1^(2k)` gives
  `L0`, `L1`, `L2` for k = 1, 2, 3 (mod 3); from `L2` it gives `L2`, `L0`, `L1`. `L1` first makes a short trip of
  11 cells right over the tokens it has just written, so its crossings depend on them.
- **The turn: E on `u`.** When the right sweep, in E, meets `u`, the head turns left into the blocks it has just
  written. This excursion either comes back right past the `u` and the sweep goes on in state C, or runs all the way
  to the left end and ends the lap. In 3·10^8 steps: 1,913 excursions came back, after going 10 to 200 cells left
  (most 10 to 20; `c/excursions.c`), and 3,097 ended the lap. Which one happens is not decided by the tokens to the
  right of the `u`; it depends on the blocks to its left.
- **The zone.** Between the turning point and the right end (absolute -659 to +228 after 2·10^9 steps) the tokens
  look irregular, with runs of up to about 15 `u` in a row. The right end set records at laps 346,
  521, 622, 1,145, 1,736 and 2,578 (cell 228) and none in the 5,700 laps after that; the zone grows at its left edge
  instead (the shallowest turning point went from about -220 at 2·10^7 steps to -659 at 2·10^9).
- **Where it can halt.** F reading 0. F is entered only from E reading 0, and E from D reading 0 or F reading 1, so
  going left E and F alternate across `0 1` pairs, and a halt needs that zigzag to meet two 0s in the wrong phase.
  The blocks `1^(2k) 0` (k ≥ 1) have single 0s, and every crossing in `lean/RightPass.lean` and
  `lean/LeftPass.lean` is a run without a halt, so the risk sits in the zone and in the excursions.

## Why the busycoq #115 method does not fit as it stands

In PRs 115 to 119 each sweep runs over the whole list and brings back a carry with three values, and an invariant on
the front of the list closes. Here the sweeps are transducers too, and the left sweep does count mod 3, but the
recursion sits elsewhere: the turning point is wherever an `E`-`u` excursion fails to come back, and excursions nest
inside the right sweep at varying depths. A proof along these lines needs (1) the excursion as a third transducer,
(2) a description of which token words the zone can hold, closed under one lap, and (3) the right sweep and the
left sweep over the body chained into the copy. (3) is within reach with the Lean files here; (2) is the hard part,
and the zone looks irregular, the tracker's "chaotic edge".

## For later

- The `L1` crossing with its 11-cell trip as a rule on tokens, then the left sweep over the body as a list theorem
  like `pass_sound`, and the body copy (3) as a theorem.
- The `E`-`u` excursion as a transducer: find the states the left-moving head can be in during an excursion and the
  condition that sends it back right.
- With both, the lap is a map on token words; then look for the language of the zone (or a potential) on that map.

## First look

Growth class **fixed/sqrt** (left: sqrt, exponent 0.499; right: fixed,
exponent 0.048). After 1,000,000,000 steps: 29,507 cells visited (21,488 left of the
start, 228 right), 17,521 ones.

- left, step 972,854,861: `B>0 1 0^3 1 0^2 1 0^2 1 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0 1^2 0 1^2 0 1 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0 1^2 0 1^2 0 1 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0 1^2 0 1^2 0 1 0 1^2 0 1^2 0 1^2 0 1 0 1^2 0^2 1 0 `
- left, step 988,763,938: `B>0 1 0^3 1 0^2 1 0^2 1 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0 1^2 0 1^2 0 1 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0 1^2 0 1^2 0 1 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0 1^2 0 1^2 0 1 0 1^2 0 1^2 0 1^2 0 1 0 1^2 0^2 1 0 `

## Pages

- [`pages/holdouts/1RB0LD_1RC0RD_1LA0RC_1RE1LB_1LF0LA_---0LE/explainer.html`](../../pages/holdouts/1RB0LD_1RC0RD_1LA0RC_1RE1LB_1LF0LA_---0LE/explainer.html)
- [`pages/holdouts/1RB0LD_1RC0RD_1LA0RC_1RE1LB_1LF0LA_---0LE/proof-status.html`](../../pages/holdouts/1RB0LD_1RC0RD_1LA0RC_1RE1LB_1LF0LA_---0LE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LD_1RC0RD_1LA0RC_1RE1LB_1LF0LA_---0LE/lean/check.sh
```
