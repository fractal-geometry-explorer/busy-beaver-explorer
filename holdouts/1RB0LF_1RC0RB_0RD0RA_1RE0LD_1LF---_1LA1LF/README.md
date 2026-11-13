# 1RB0LF_1RC0RB_0RD0RA_1RE0LD_1LF---_1LA1LF

bbchallenge id 51276, group G10 (one side grows like √t, the other like a smaller power). Family: **bouncer over a 10 background with a defect gas**. Halting from blank tape: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 1RC | 0RB |
| C | 0RD | 0RA |
| D | 1RE | 0LD |
| E | 1LF | --- |
| F | 1LA | 1LF |

## What it does

The left side is the plain `10` background of a bouncer: rightward passes in A/B/C shift every copy of `1010` to `0101` or back (proved shift rules), leftward passes in A/F leave it as it is. The left end grows like the square root of the step count.

The right end (slow side, exponent about 0.23) is where the action is: near it the background carries defects. Written as runs of 1s (numbers) and gaps (`.` one 0, `:` two 0s, `_k` k 0s), the last 40 runs at step 982,617,644 are `2 . 1 . 1 . 1 : 1 . 1 . 1 . 1 _4 1 . 1 . 1 … 1 _6 1 . 1 .`. Defects appear at the right wall, travel and merge; their pattern has no visible period.

## Halting

E reading 1 halts. In the 5-cell closed language this needs `1010x` on the left and a 1 under the head; every right window starting with 1 is allowed, so the language does not locate the halt.

Closed tape language with 5-cell windows (`python3 -m bbtools.ctl M 5`, trusted Python check): a halt (E reading 1) needs `10100`, `10101` or `10110` to the left (nearest first); any right side starting with 1.

## What is proved

- `lean/Blank.lean` (generated): the halting configurations (`step_none_iff`); no halt in 10,000 steps (kernel) and 10^7 steps (`native_decide`).
- `lean/Sweeps.lean`: 8 shift rules, kernel-checked: B, C and A shift `1010`↔`0101` rightward, A and F cross `10`/`01` leftward unchanged (`sweep_lA_10_1`, `sweep_lF_01_0`, `sweep_lA_1010_1`, `sweep_rB_1010`, `sweep_rC_1010`, `sweep_rA_0101`, `sweep_rB_0101`, `sweep_lF_0101_0`). Found by trying every state and direction on one copy of each background word with `bbtools.symtm` (`_one_copy_right`, `_one_copy_left`), then `symtm.prove`.

Everything else here is observation of the run (heuristic) or a trusted computation, as marked in `status.json`. Nothing proved here decides halting.

## Evidence and how to reproduce

```sh
./tmrun 1RB0LF_1RC0RB_0RD0RA_1RE0LD_1LF---_1LA1LF 1000000000 records 100000      # tapes at each new cell
./tokrun 1RB0LF_1RC0RB_0RD0RA_1RE0LD_1LF---_1LA1LF 1000000000 a=10,b=110 L 100000 # the tape as words at the left end (R for the right)
python3 -m bbtools.ctl 1RB0LF_1RC0RB_0RD0RA_1RE0LD_1LF---_1LA1LF 5                # (from tools/py) the closed language and its halts
```

## For later

Compare with the part03 twin (one transition differs): if their right-end defect sequences coincide, the defect mechanism is in the shared states.

## First look

Growth class **power/sqrt** (left: sqrt, exponent 0.526; right: power,
exponent 0.233). After 1,000,000,000 steps: 36,408 cells visited (23,764 left of the
start, 3,404 right), 18,247 ones.

- left, step 970,588,675: `F>0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- left, step 986,327,673: `F>0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- right, step 897,725,480: `1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- right, step 982,617,641: `1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `

## Pages

- [`pages/holdouts/1RB0LF_1RC0RB_0RD0RA_1RE0LD_1LF---_1LA1LF/explainer.html`](../../pages/holdouts/1RB0LF_1RC0RB_0RD0RA_1RE0LD_1LF---_1LA1LF/explainer.html)
- [`pages/holdouts/1RB0LF_1RC0RB_0RD0RA_1RE0LD_1LF---_1LA1LF/proof-status.html`](../../pages/holdouts/1RB0LF_1RC0RB_0RD0RA_1RE0LD_1LF---_1LA1LF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LF_1RC0RB_0RD0RA_1RE0LD_1LF---_1LA1LF/lean/check.sh
```
