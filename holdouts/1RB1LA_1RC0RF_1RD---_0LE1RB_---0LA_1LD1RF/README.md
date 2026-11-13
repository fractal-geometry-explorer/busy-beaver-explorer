# 1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF

bbchallenge id 118184. One of the six-state holdouts whose halting from blank tape is open (group G10). Family: **merging and splitting blocks of 1s (chaotic, potential Cryptid)**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LA |
| B | 1RC | 0RF |
| C | 1RD | --- |
| D | 0LE | 1RB |
| E | --- | 0LA |
| F | 1LD | 1RF |

## What it does

The visited tape is always a few (3 to 9) blocks of 1s separated by single 0s. Sweeps move material between neighbouring blocks: blocks merge, and chains of near-doubling lengths appear (97, 198, 397, 795), then dissolve. Both ends grow slowly (4,515 cells in 10^9 steps), in single cells on the left and bursts of 2 to 7 on the right. It looks like an iterated map on a short list of numbers with doubling: the bbchallenge wiki lists it as a potential Cryptid (chaotic).

```
the tape at the right end (1^k a = 1^(k+1) 0):
step  61,625,383  F 1^102 a 1^97 a 1^198 a 1^397 a 1^795 a 1^122 a 1^9
step 123,727,894  F 1^1014 a 1^1009 a 1^149 a 1^41 a 1^5
step 184,076,659  F 1^433 a 1^1266 a 1^832 a 1^34
step 245,968,753  F 1^313 a 1^308 a 1^620 a 1^653 a 1^809 a 1^125 a 1^10
```

## Halting

Two halting transitions, C1 and E0. Lean (`lean/LeftEdge.lean`, a closed tape language of windows of 6 cells from `bbtools.ctl`, closure by `native_decide`): every halt from blank tape has exactly `1 1 1 1 1` and then blank tape to the left of the head (`halt_left`), i.e. it happens within six cells of the left end. Deciding needs the block map.

## Status

**Open.** Lean: `lean/LeftEdge.lean` with `lean/EdgeCert.lean` (a closed tape language of windows of 6 cells from `bbtools.ctl`; closure and halting check by `native_decide`, the automaton lemmas by the kernel): every halt from blank tape has exactly `1 1 1 1 1` and then blank tape to the left of the head (`halt_left`). Plus the generated `lean/Blank.lean`.
Deciders tried without success: `bbtools.ctl` with windows K = 2..6 (no closed language without halts), `ngramcps`
with widths 2..6, plain and with `-H 2`, `-H 3`, `-U`.

## For later

- Extract the block map: sample the block list at each right-end turn and find how a sweep changes it (which
  blocks merge, which split), as an explicit map on the list of block lengths. If it is Collatz-like, say so.
- `cert_closed` (3,984 abstract configurations) runs out of memory under `decide +kernel` here; a smaller
  language or a kernel-friendlier check would make the left-end result kernel-only.

## Pages

- [`pages/holdouts/1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF/explainer.html`](../../pages/holdouts/1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF/explainer.html)
- [`pages/holdouts/1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF/proof-status.html`](../../pages/holdouts/1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF/proof-status.html)
