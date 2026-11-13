# 1RB1LC_1LA---_1LD0LA_1RE0LE_0RF1RE_1LB1RD

bbchallenge id 147121, a BB(6) holdout (group G06). Family: **doubling phases on a growing junk tape**. Open; a
provable loop at the right end, steered by an irregular tape further left.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LC |
| B | 1LA | --- |
| C | 1LD | 0LA |
| D | 1RE | 0LE |
| E | 0RF | 1RE |
| F | 1LB | 1RD |
## What it does

The left end of the tape stays put; the action is at the right end. A **phase** starts when the head, in state E,
reaches a new cell at the right end of

    L 1 0 1^P 0 (10)^Q 1^5 E> 0^inf          (Q = 2 at the start of a phase)

* `round` (`lean/Rules.lean`): `L 1 0 1^(p+7) 0 (1010)^(q+1) 1^5 E> 0^inf` -> `L 1 0 1^(p+5) 0 (1010)^(q+2) 1^5 E> 0^inf`
  in 28q+64 steps, for every p, q and every tape L: (P, Q) -> (P-2, Q+2) for P >= 7 and even Q >= 2;
* `rounds` (`lean/Rounds.lean`, induction): k rounds, (P+2k, Q) -> (P, Q+2k).

A phase with P ones costs about 3.5 P^2 steps. When the ones run out the head walks into the tape left of the block
and starts the next phase: often with P = 9, sometimes with `P' = 2P + 11`, which can repeat (37, 85, 181, 373,
757, ..., 3,145,717: 16 doublings in a row). With odd Q the round rule does not hold (the head turns into the ones;
checked on small cases) and the phase ends differently; this happens rarely.

What decides the next phase is the tape left of the block, a long irregular mixture of short words (`1^3 0`,
`1^7 0`, `1110`, ...) that the phase ends rewrite and that grows with the phases. No regular structure has been
found in it.

### What decides doubling or reset (`py/phase_ends.py`)

For each of the first 36 phases the tape after the rounds is copied and the phase end is run on it alone, recording
how far left of the block the head goes. Two kinds:

* **Short ends** read at most 56 cells and give P' = 2P + c, c set by those cells. The 14 cells `1110 11111 0 1010`
  give c = 11 and are left in place again, so the doubling repeats (37, 85, 181, ...; phases 28 to 36); other
  contexts gave c = 27, 15, 19, 5, -11, 31, 19.
* **Long ends** (24 of the 36) cross the whole tape left of the block, run into the blank tape beyond it, and give
  P' in {9, 29, 41, 65, 169}, whatever P was. They rewrite the whole left tape; the irregular words come from them.

So a doubling streak lasts while the cells next to the block allow a short end. Not yet done: the rules for the
short ends with symbolic Q (symtm stops with `NeedSplit` on `(10)^q`: the phase end turns the 10's into 1111's by
zigzag passes, which needs an induction of its own), and a description of what a long end leaves.

## Status

Open.

* Lean: `lean/Blank.lean` (halting configurations, no halt in 10^4 steps by the kernel, 10^7 by `native_decide`),
  `lean/Rules.lean`, `lean/Rounds.lean` (above).
* `py/phases.py` (exact accelerated simulator `py/tsim.py`, rounds skipped by the Lean rule for even Q only): 156
  phases, more than 3*10^13 steps (the phase with P = 3,145,717 alone is about 3.5*10^13), no halt. P = 9 starts 69
  of them.
* The only halting transition is B reading 1; the rounds cannot halt, so a halt would come at a phase end.

## For later

* Describe the tape left of the block (the words and how a phase end rewrites them); without that the next phase
  can only be simulated.
* Prove the phase ends that start a doubling (`P' = 2P + 11`) and the reset to 9 as symtm rules for the words they meet.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LC_1LA---_1LD0LA_1RE0LE_0RF1RE_1LB1RD/lean/check.sh
python3 holdouts/1RB1LC_1LA---_1LD0LA_1RE0LE_0RF1RE_1LB1RD/py/phases.py 156 1
python3 holdouts/1RB1LC_1LA---_1LD0LA_1RE0LE_0RF1RE_1LB1RD/py/phase_ends.py 36   # depth of each phase end, 20 minutes
```

## Pages

- [`explainer.html`](../../pages/holdouts/1RB1LC_1LA---_1LD0LA_1RE0LE_0RF1RE_1LB1RD/explainer.html)
- [`proof-status.html`](../../pages/holdouts/1RB1LC_1LA---_1LD0LA_1RE0LE_0RF1RE_1LB1RD/proof-status.html)
