# 1RB0RF_1LC0RC_0LD1LC_1RE1LB_1RF---_1LE1RA

bbchallenge id 49956, a BB(6) holdout (group G06). **Family: sweeping transducer on a block word, with a doubling chain at the
left end (proved); the rest of the word is not decoded.**

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RF |
| B | 1LC | 0RC |
| C | 0LD | 1LC |
| D | 1RE | 1LB |
| E | 1RF | --- |
| F | 1LE | 1RA |

## What it does

The head sweeps the whole tape; at each end the tape is a word over `1` and `a = 10`, which every sweep rewrites
(early on: `1^6 a 1^10 a 1^7`, `1^8 a^6 1^11`, `1^2 a^4 1^12 a^5`, ...). Between the sweeps there are long stretches
spent at the left end, after which one block of ones fills much of the tape (`1^102` at step 11,869, `1^1730` at
3,472,160, `1^49142` at 2,820,772,373).

### The left end: transfer and doubling chain (proved)

Write G for the left end `0^inf 1 1 1 0 1 0 1 1 0` with the head in C on a 0.

* **Transfer** (`transfer`, `lean/Rules.lean`): `G (10)^(2j+1) 1^3 R -> G (10)^(2j+3) 1 R` in 28j+64 steps, for
  every j and every tape R. Two ones become two more copies of `10` and the tape grows by two cells on the left.
  n transfers cost n(28j+14n+50) steps (`transfer_n`, `cost_eq`, `lean/Transfer.lean`): a block of m ones is
  emptied in about 3.5 m^2 steps, which is nearly all of the running time.
* **Doubling** (`double7`, `chain7`): `G 10 1^x (10)^3 1^5 0 1^7 0 R -> G 10 1^(2x+12) (10)^3 1^5 0 R` for even
  x >= 2. The item `1^7 0` is used up; c items in a row give c doublings, 2^c (x+12) - 12 ones (`chain`, `dbl_eq`).

Observed chains (ones in the block, counting the first one of the following `(10)^3`): 181, 373, 757, 1525, 3061,
6133, 12277, 24565 (steps 4.9e6 to 2.8e9); later 3061, ..., 786429 (ending at step 2.9e12) and 3061, ..., 786421
(5.8e12).

### Not decoded

How many items `1^7 0` stand after the block is decided by the sweeps over the rest of the word (`1^3 0`, `1^5 0`,
`1^7 0`, `a^k`, ... in changing periodic patterns). They act like a fixed transducer applied at each pass; its
rules have not been extracted. The machine halts only from the head in D on a 0 followed by `1` or by `0 0`.

## Status

Open. Proved in Lean: the transfer and the doubling chain, for all parameters. Trusted: no halt to 7.3e12 steps
(`c/transfer.c`, which applies the transfer in closed form; checked against the plain machine by
`py/check_transfer.py`). Others report simulations to 2.4e14 steps.

## For later

* Extract the transducer of one sweep (left to right in F/A, right to left in C/D/B) as symtm rules on the items
  `1^(2i+1) 0` and `a^k`, and find how a run of items `1^7 0` is produced. The length of each chain, hence the
  giant blocks, would follow.
* `c/transfer.c` still steps through the sweeps cell by cell (5e6 cells wide at 7e12 steps); a run-length tape
  with the sweep transducer would go much further.

## Pages

- [`pages/holdouts/1RB0RF_1LC0RC_0LD1LC_1RE1LB_1RF---_1LE1RA/explainer.html`](../../pages/holdouts/1RB0RF_1LC0RC_0LD1LC_1RE1LB_1RF---_1LE1RA/explainer.html)
- [`pages/holdouts/1RB0RF_1LC0RC_0LD1LC_1RE1LB_1RF---_1LE1RA/proof-status.html`](../../pages/holdouts/1RB0RF_1LC0RC_0LD1LC_1RE1LB_1RF---_1LE1RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RF_1LC0RC_0LD1LC_1RE1LB_1RF---_1LE1RA/lean/check.sh
gcc -O2 -o sweeps holdouts/1RB0RF_1LC0RC_0LD1LC_1RE1LB_1RF---_1LE1RA/c/sweeps.c && ./sweeps 3000000000 1000
gcc -O2 -o transfer holdouts/1RB0RF_1LC0RC_0LD1LC_1RE1LB_1RF---_1LE1RA/c/transfer.c && ./transfer 10000000000000 150 1000
python3 holdouts/1RB0RF_1LC0RC_0LD1LC_1RE1LB_1RF---_1LE1RA/py/check_transfer.py
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1LC_1LA---_1LD0LA_1RE0LE_0RF1RE_1LB1RD`](../1RB1LC_1LA---_1LD0LA_1RE0LE_0RF1RE_1LB1RD/README.md): rename A→C, B→D, C→E, D→F, E→B, F→A and exchange left and right; it is this table started in state F, in a mirror

<!-- end of related machines -->
