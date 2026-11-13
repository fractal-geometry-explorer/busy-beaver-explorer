# 1RB0LF_1RC0RB_0RD0RA_1RE1LE_1RF---_1LA1LF

bbchallenge id 129932. A big block (10)^B grows at the left end and is copied down a cascade of blocks of sizes about B/4, B/4, B/8, B/16, B/32, ..., which ends in an irregular region on the right that grows slowly.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 1RC | 0RB |
| C | 0RD | 0RA |
| D | 1RE | 1LE |
| E | 1RF | --- |
| F | 1LA | 1LF |

## What it does

The left side grows like √t: a block `(10)^B` at the left end gains a cell on most sweeps. Behind it the tape is a
**cascade** of blocks whose sizes halve. At step 972,317,882 (compressed, `(10)^5` is `10` five times):

    (10010)^2 (10)^8343 (01010)^2 (10)^4 (01)^2089 (10)^4 (01)^2086 (00101)^2 (01)^18 0^4 (10)^1063 1 (10)^4
    (01)^10 (10)^527 (01)^10 0 (01)^4 (10)^6 1 (10)^271 (01)^4 0 (01)^211 (10)^88 (01)^108 …

8343, 2089, 2086, 1063, 527, 271: about B, B/4, B/4, B/8, B/16, B/32. Near step 2·10⁹ it is 11,949 | 2,989
2,989 | 1,514 | 751 | 382, the same proportions, all growing with B. Below a few hundred the cascade turns into an
**irregular end** (blocks of 10 to 100, walls `0^3`, `0^4`, `1^3`, `1^4`), which is most of the right side; it
grows slowly (t^0.20).

In plain words: a binary counter whose high digits are long, clean blocks (each half the size of the one before)
and whose low digits are a churning mess at the far end.

## What is proved

- Lean, kernel only (`lean/Blank.lean`, generated): the halting configurations (`step_none_iff`) and no halt in the first 10,000 steps; with `native_decide`, none in the first 10<sup>7</sup>.
- Lean, kernel only (`lean/Rules.lean`, written by `py/rules.py`): the shift rules of the leftward sweeps across `(10)^n` (state A) and `(01)^n` (state F) (`shift_l_A_10`, `shift_l_F_01`).
- C (`tools/c/triage.c`, trusted): no halt in the first 10<sup>9</sup> steps.

Everything else above is measured on runs (heuristic), not proved.

## Open

Whether it halts. The cascade is measured; the irregular end, where a halt would have to happen, is not
understood. Same family as 1RB0RA_1RC0RF_0RD1LE_0LE---_1LF1LE_1RA0LC in this batch (the same cascade B, B/4, B/4,
B/8, …); the batch notes pair it with 1RB0LF_1RC0RB_0RD0RA_1RE0LD_1LF---_1LA1LF (another batch), which differs in
two transitions.

## For later

More than a day. Next: (1) find the macro step that adds one cell to B and the cascade's response (does each
block grow when the next larger one passes a multiple of 2?); (2) test whether the irregular end is a fixed finite
transducer acting on a sequence of counts; (3) compare with 1RB0RA_1RC0RF_0RD1LE_0LE---_1LF1LE_1RA0LC.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LF_1RC0RB_0RD0RA_1RE1LE_1RF---_1LA1LF/lean/check.sh
python3 holdouts/1RB0LF_1RC0RB_0RD0RA_1RE1LE_1RF---_1LA1LF/py/rules.py          # rewrites lean/Rules.lean
python3 holdouts/1RB0LF_1RC0RB_0RD0RA_1RE1LE_1RF---_1LA1LF/py/observe.py 1e7 B 6  # the tape at the last moments each end grew
```

## Pages

- [`pages/holdouts/1RB0LF_1RC0RB_0RD0RA_1RE1LE_1RF---_1LA1LF/explainer.html`](../../pages/holdouts/1RB0LF_1RC0RB_0RD0RA_1RE1LE_1RF---_1LA1LF/explainer.html)
- [`pages/holdouts/1RB0LF_1RC0RB_0RD0RA_1RE1LE_1RF---_1LA1LF/proof-status.html`](../../pages/holdouts/1RB0LF_1RC0RB_0RD0RA_1RE1LE_1RF---_1LA1LF/proof-status.html)
