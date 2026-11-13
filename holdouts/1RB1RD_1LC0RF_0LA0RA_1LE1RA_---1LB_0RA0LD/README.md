# 1RB1RD_1LC0RF_0LA0RA_1LE1RA_---1LB_0RA0LD

bbchallenge id 175040. Halting from blank tape is open. The tape is a list of blocks of `0111110` separated by a few kinds of separator, like digits.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RD |
| B | 1LC | 0RF |
| C | 0LA | 0RA |
| D | 1LE | 1RA |
| E | --- | 1LB |
| F | 0RA | 0LD |

## What it does

With `p = 0111110` and `q = 011111110`, at step 5,607,797,795 (head in A at the right end):

    p 0 1^9 0^2 1^9 0^2 1^9 0 p^7782 0 1^3 0 p^3734 0 1^3 0 p^4744 0 1^9 0 p^2189 0 1^9 0 p^27 0 1^9 0 p^1381 0 1^9 0 p^993 0 1^9 0 p^150 0^2 A>

Long blocks of `p` separated by `0 1^9 0`, `0 1^3 0` or `q`. Earlier lists: 2230, 116, 160, 1051, 174 at step
1.59·10^8; 8011, 3169, 12, 311, 1467, 15, 1007, 156 at 2.82·10^9. The sweeps rewrite the tape seven cells at a time
(the Lean rules). The width grows like 2·sqrt(t) (72,388 at step 1.36·10^9, 147,106 at 5.61·10^9).

## What is proved

- Lean, kernel (`lean/Rules.lean`, from `py/rules.py`): the sweep rules

    L A> (0101111)^n R -> L (1001111)^n A> R
    L D> (1010111)^n R -> L (1100111)^n D> R
    L D> (1110101)^n R -> L (1111001)^n D> R
    L F> (0111101)^n R -> L (0111110)^n F> R
    L B> (1011110)^n R -> L (0011111)^n B> R
    L A> (1101011)^n R -> L (1110011)^n A> R
    L A> (1111010)^n R -> L (1111100)^n A> R
    L A> (0011111)^n R -> L (0111111)^n A> R

- Lean (`lean/Blank.lean`, generated): the halting configurations, no halt in 10^4 / 10^7 steps.

Everything under "What it does" is observation from simulation, not proof.

## Open

Halting. How a round trip changes the separators and blocks is not known.

## For later

- Follow one round trip at the level of blocks and separators, and write it as a map on the list.

## Reproduce

```sh
tools/c/tokrun 1RB1RD_1LC0RF_0LA0RA_1LE1RA_---1LB_0RA0LD 6000000000 p=0111110,q=011111110,r=011111111110 LR 100000
python3 holdouts/1RB1RD_1LC0RF_0LA0RA_1LE1RA_---1LB_0RA0LD/py/rules.py > holdouts/1RB1RD_1LC0RF_0LA0RA_1LE1RA_---1LB_0RA0LD/lean/Rules.lean
. /etc/profile.d/lean.sh && holdouts/1RB1RD_1LC0RF_0LA0RA_1LE1RA_---1LB_0RA0LD/lean/check.sh
```

## Pages

- [`pages/holdouts/1RB1RD_1LC0RF_0LA0RA_1LE1RA_---1LB_0RA0LD/explainer.html`](../../pages/holdouts/1RB1RD_1LC0RF_0LA0RA_1LE1RA_---1LB_0RA0LD/explainer.html)
- [`pages/holdouts/1RB1RD_1LC0RF_0LA0RA_1LE1RA_---1LB_0RA0LD/proof-status.html`](../../pages/holdouts/1RB1RD_1LC0RF_0LA0RA_1LE1RA_---1LB_0RA0LD/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LF_0RC0LC_1LA1LD_1RE1LC_---1RA_0LC0RD`](../1RB0LF_0RC0LC_1LA1LD_1RE1LC_---1RA_0LC0RD/README.md): rename A→C, B→A, C→B, D→D, E→E, F→F and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
