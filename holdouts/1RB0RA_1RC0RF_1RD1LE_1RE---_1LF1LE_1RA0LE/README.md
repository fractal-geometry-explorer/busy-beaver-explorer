# 1RB0RA_1RC0RF_1RD1LE_1RE---_1LF1LE_1RA0LE

bbchallenge id 111043. Halting from blank tape is open. The tape is hundreds of blocks of `10` with roughly halving large blocks at the left.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RA |
| B | 1RC | 0RF |
| C | 1RD | 1LE |
| D | 1RE | --- |
| E | 1LF | 1LE |
| F | 1RA | 0LE |

## What it does

With `a = 10` and `b = 110`, at the moments the head extends the tape, the tape is a list of blocks `a^x` separated
by `0`, `0^3`, `b` or `1^2 b`. At step 9,866,788,243:

    E> 0 a^6 b a^26719 b a^3 b a^6 b a^6670 0 a^10 0 a^6669 b a^4 b a^18 0 a^3334 0 a^7 b a^43 1^2 b a^1683 ...

453 blocks; the largest are 26719, 6670, 6669, 3334, 1683, 823, 630, 525 (roughly halving), and 377 are shorter
than 20. The width grows like 1.14·sqrt(t) (32,845 at step 8.0·10^8, 112,986 at 9.87·10^9).

## What is proved

- Lean, kernel (`lean/Rules.lean`, from `py/rules.py`): the sweep rules

    L (01)^n E> 0 R -> L E> 0 (01)^n R
    L (10)^n F> 1 R -> L F> 1 (10)^n R
    L (1010101)^n F> 1 R -> L F> 1 (1010110)^n R
    L A> (10101)^n R -> L (01010)^n A> R
    L (10101)^n F> 1 R -> L F> 1 (10110)^n R
    L A> (0101010)^n R -> L (1010101)^n A> R
    L (101)^n F> 1 R -> L F> 1 (110)^n R
    L A> (1)^n R -> L (0)^n A> R

- Lean (`lean/Blank.lean`, generated): the halting configurations, no halt in 10^4 / 10^7 steps.

Everything under "What it does" is observation from simulation, not proof.

## Open

Halting. No rule for the blocks is known; the halving sizes suggest a binary counter but this is not established.

## For later

- Track the large blocks only (sizes above 500) from extension to extension and look for a carry rule.

## Reproduce

```sh
tools/c/tokrun 1RB0RA_1RC0RF_1RD1LE_1RE---_1LF1LE_1RA0LE 10000000000 a=10,b=110 LR 100000
python3 holdouts/1RB0RA_1RC0RF_1RD1LE_1RE---_1LF1LE_1RA0LE/py/rules.py > holdouts/1RB0RA_1RC0RF_1RD1LE_1RE---_1LF1LE_1RA0LE/lean/Rules.lean
. /etc/profile.d/lean.sh && holdouts/1RB0RA_1RC0RF_1RD1LE_1RE---_1LF1LE_1RA0LE/lean/check.sh
```

## Pages

- [`pages/holdouts/1RB0RA_1RC0RF_1RD1LE_1RE---_1LF1LE_1RA0LE/explainer.html`](../../pages/holdouts/1RB0RA_1RC0RF_1RD1LE_1RE---_1LF1LE_1RA0LE/explainer.html)
- [`pages/holdouts/1RB0RA_1RC0RF_1RD1LE_1RE---_1LF1LE_1RA0LE/proof-status.html`](../../pages/holdouts/1RB0RA_1RC0RF_1RD1LE_1RE---_1LF1LE_1RA0LE/proof-status.html)
