# 1RB0RD_1LC0RA_1LA0LB_1RE0LC_1RA1RF_0RB---

bbchallenge id 93459. Halting from blank tape is open. Active phases drain a right-end block into a left counter, one unit per bounce; rebuild phases make a new block.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RD |
| B | 1LC | 0RA |
| C | 1LA | 0LB |
| D | 1RE | 0LC |
| E | 1RA | 1RF |
| F | 0RB | --- |

## What it does

With `w = 1010110` and `a = 10`, at left extensions in an active phase the tape is `0 0 w^n <middle> 1 a^k w`.
Each bounce adds one `w` at the left and removes one `a` from the right block:

    step 302,136,397     n = 648     k = 10159
    step 1,001,302,397   n = 5848    k = 4959
    step 2,126,686,397   n = 10648   k = 159

When the block is used up, the head stops reaching the left end (steps 2.17·10^9 to 3.85·10^9) and builds a new
right block from the middle of the tape, which is hierarchical: `(a^2 w a^10 w)^m`, `(a^8 w a^40 w)^m`, and a few large
blocks (21, 333, 922, 530, 2289, ...). Active phases started at steps 24.4·10^6 (block 569), 295.8·10^6 (10236) and
3.85·10^9 (6363).

## What is proved

- Lean, kernel (`lean/Rules.lean`, from `py/rules.py`): the sweep rules

    L A> (01)^n R -> L (10)^n A> R
    L (01)^n B> 0 R -> L B> 0 (01)^n R
    L B> (10)^n R -> L (01)^n B> R
    L (10)^n C> 1 R -> L C> 1 (10)^n R
    L A> (1010101)^n R -> L (0110010)^n A> R
    L A> (10101)^n R -> L (01100)^n A> R
    L A> (0110101)^n R -> L (1001100)^n A> R
    L B> (1101010)^n R -> L (0011001)^n B> R

- Lean (`lean/Blank.lean`, generated): the halting configurations, no halt in 10^4 / 10^7 steps.

Everything under "What it does" is observation from simulation, not proof.

## Open

Halting. The rebuild phase (how the middle part turns into the next right block) is not understood.

## For later

- Follow one rebuild phase at the level of the middle hierarchy and find the map from one active phase's start
  configuration to the next.

## Reproduce

```sh
tools/c/tokrun 1RB0RD_1LC0RA_1LA0LB_1RE0LC_1RA1RF_0RB--- 6000000000 w=1010110,a=10 L 100000     # left extensions
python3 holdouts/1RB0RD_1LC0RA_1LA0LB_1RE0LC_1RA1RF_0RB---/py/rules.py > holdouts/1RB0RD_1LC0RA_1LA0LB_1RE0LC_1RA1RF_0RB---/lean/Rules.lean
. /etc/profile.d/lean.sh && holdouts/1RB0RD_1LC0RA_1LA0LB_1RE0LC_1RA1RF_0RB---/lean/check.sh
```

## Pages

- [`pages/holdouts/1RB0RD_1LC0RA_1LA0LB_1RE0LC_1RA1RF_0RB---/explainer.html`](../../pages/holdouts/1RB0RD_1LC0RA_1LA0LB_1RE0LC_1RA1RF_0RB---/explainer.html)
- [`pages/holdouts/1RB0RD_1LC0RA_1LA0LB_1RE0LC_1RA1RF_0RB---/proof-status.html`](../../pages/holdouts/1RB0RD_1LC0RA_1LA0LB_1RE0LC_1RA1RF_0RB---/proof-status.html)
