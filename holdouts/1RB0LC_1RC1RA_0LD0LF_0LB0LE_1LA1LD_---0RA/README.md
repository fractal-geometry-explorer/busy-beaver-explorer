# 1RB0LC_1RC1RA_0LD0LF_0LB0LE_1LA1LD_---0RA

bbchallenge id 91338, group G10 (one side grows like √t, the other like a smaller power). Family: **bouncer with a wandering solid block**. Halting from blank tape: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1RC | 1RA |
| C | 0LD | 0LF |
| D | 0LB | 0LE |
| E | 1LA | 1LD |
| F | --- | 0RA |

## What it does

The tape has three parts. Far left: the `10` background of a bouncer that grows to the left like the square root of the step count. Far right (the slow side, 115 cells right of the start after 10^9 steps): a periodic pattern `(1111 0 1 0 1 0)` repeated, which only grows by a cell now and then. In between: one or two *solid blocks* of 1s, thousands of cells long, separated by stretches of `10`.

Rightward sweeps fill `10` into `11` (rules `sweep_rB_10`, `sweep_rA_01`), leftward sweeps cut solid stretches back into `10` or `0010`. So the solid block is moved, grown and cut: e.g. at step 4·10^7 the tape reads `1^3 0 (10)* 1 0 1^964 0 (10)* 1 0 1 0 1^1388 E> (10)* …`, at 3·10^8 `1^7533 B> (10)* …` (a single block), at 5.4·10^8 `1^6847 0 (10)* 1 0 1^925 A>0 (10)* …`.

Each time a block runs into the right part, the right end gets a few new cells, which is why the slow side grows in rare steps (right extent ~ t^0.13). The lengths of the blocks look irregular; we have no rule for them.

## Halting

F reading 0 halts. The 5-cell closed language allows this only with `00010` to the right of the head.

Closed tape language with 5-cell windows (`python3 -m bbtools.ctl M 5`, trusted Python check): a halt (F reading 0) needs `00010` to the right of the head; any left side.

## What is proved

- `lean/Blank.lean` (generated): the halting configurations (`step_none_iff`); no halt in 10,000 steps (kernel) and 10^7 steps (`native_decide`).
- `lean/Sweeps.lean`: 10 shift rules, kernel-checked: B and A turn `10`/`01` into `11` rightward (filling a block), C, D and E erase leftward (`0101` → `0100`, `1010` → `0010` …) (`sweep_rB_10`, `sweep_rA_01`, `sweep_rB_01`, `sweep_lA_1010_1`, `sweep_rB_1010`, `sweep_lD_1010_1`, `sweep_rA_0101`, `sweep_rB_0101`, `sweep_lC_0101_0`, `sweep_lE_0101_0`). Found by trying every state and direction on one copy of each background word with `bbtools.symtm` (`_one_copy_right`, `_one_copy_left`), then `symtm.prove`.

Everything else here is observation of the run (heuristic) or a trusted computation, as marked in `status.json`. Nothing proved here decides halting.

## Evidence and how to reproduce

```sh
./tmrun 1RB0LC_1RC1RA_0LD0LF_0LB0LE_1LA1LD_---0RA 1000000000 records 100000      # tapes at each new cell
./tokrun 1RB0LC_1RC1RA_0LD0LF_0LB0LE_1LA1LD_---0RA 1000000000 a=10,b=110 L 100000 # the tape as words at the left end (R for the right)
python3 -m bbtools.ctl 1RB0LC_1RC1RA_0LD0LF_0LB0LE_1LA1LD_---0RA 5                # (from tools/py) the closed language and its halts
```

## For later

Sample the run each time a solid block is born or dies, record the block lengths, and look for a map between them (the staircase suggests a Collatz-like map on the block length).

## First look

Growth class **power/sqrt** (left: sqrt, exponent 0.453; right: power,
exponent 0.131). After 1,000,000,000 steps: 40,882 cells visited (30,269 left of the
start, 115 right), 26,599 ones.

- left, step 902,978,970: `E>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- left, step 918,624,204: `E>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- right, step 887,254,853: `1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- right, step 919,603,550: `1^13753 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `

## Pages

- [`pages/holdouts/1RB0LC_1RC1RA_0LD0LF_0LB0LE_1LA1LD_---0RA/explainer.html`](../../pages/holdouts/1RB0LC_1RC1RA_0LD0LF_0LB0LE_1LA1LD_---0RA/explainer.html)
- [`pages/holdouts/1RB0LC_1RC1RA_0LD0LF_0LB0LE_1LA1LD_---0RA/proof-status.html`](../../pages/holdouts/1RB0LC_1RC1RA_0LD0LF_0LB0LE_1LA1LD_---0RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1RC1RA_0LD0LF_0LB0LE_1LA1LD_---0RA/lean/check.sh
```

## Accelerated run

Trusted computation: `python3 tools/py/bbtools/rleaccel.py 1RB0LC_1RC1RA_0LD0LF_0LB0LE_1LA1LD_---0RA 4 167200000` runs 167,200,000 macro steps from blank tape without a halt, more than 9.85·10^277
machine steps (tape: about 9.09·10<sup>138</sup> cells). The simulator codes the tape in runs, crosses a run in one step and jumps cycles whose
one-cycle rule it has first proved symbolically; it is tested cell for cell against direct runs
(`tools/tests/test_rleaccel.py`).

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RE_0LC0LF_0LA0LD_1LE1LC_1RA0LB_---0RE`](../1RB1RE_0LC0LF_0LA0LD_1LE1LC_1RA0LB_---0RE/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F; it is this table started in state B

<!-- end of related machines -->
