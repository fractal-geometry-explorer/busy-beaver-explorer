# 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF

bbchallenge id 50436, group G10 (one side grows like √t, the other like a smaller power). Family: **bouncer with a sorted list of blocks 1^(6j+1)**. Halting from blank tape: **open**. It is the table of DeepMind's halting proof in busycoq PR 93 with the halt moved (see *PR 93's engine* below).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RE |
| B | 1RC | 0RF |
| C | 0LD | --- |
| D | 1LE | 1LD |
| E | 1RA | 0LB |
| F | 0RE | 0RF |

## What it does

Left of the start: `(110 10 10 10)` repeated, a √t bouncer (proved shift rules). Right of it, on the slow side (394 cells after 10^9 steps), a list of blocks of 1s separated by `00` whose settled lengths are 6j + 1, sorted, with 6j + 5 blocks at group boundaries, e.g. at step 945,073,674: `41 : 43 : 43 : 43 : 43 : 43 : 43 : 43 : 43 : 43 : 7 : 1 : 47 : 49 : 49 : 11 : 1 : 53 : 55 : 59 : 5 : 1 : 1 : 3 : 1` (run lengths, `:` = 00).

The first records coincide with those of 1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD--- (same block lists, different step counts: the two machines share the mechanism with different costs per pass); after a while the two runs diverge but keep the same structure.

## Halting

C reading 1 halts. The 5-cell closed language allows that with `11100`/`11111` on the left and any right window starting with 1.

Closed tape language with 5-cell windows (`python3 -m bbtools.ctl M 5`, trusted Python check): a halt (C reading 1) needs `11100` or `11111` to the left; any right side starting with 1.

## What is proved

- `lean/Blank.lean` (generated): the halting configurations (`step_none_iff`); no halt in 10,000 steps (kernel) and 10^7 steps (`native_decide`).
- `lean/Detour.lean`, `lean/PR93Rules.lean`: the detour and 44 macro rules of PR 93's engine for this machine (see *PR 93's engine*).
- `lean/HaltRoute.lean`: the four steps before any halt are forced; a halt needs E moving right onto `0 0 0 1` (`pre_halt`, `pre_halt_from`).
- `lean/Sweeps.lean`: 8 shift rules, kernel-checked: A crosses `110101010` rightward writing `001111111`, D crosses it leftward writing `111011101` (eight proved rules over its rotations) (`sweep_rA_110101010`, `sweep_rB_110101010`, `sweep_lD_110101010_1`, `sweep_rA_101010110`, `sweep_lE_101010110_1`, `sweep_rA_011010101`, `sweep_lD_011010101_0`, `sweep_rE_011010101`). Found by trying every state and direction on one copy of each background word with `bbtools.symtm` (`_one_copy_right`, `_one_copy_left`), then `symtm.prove`.

Everything else here is observation of the run (heuristic) or a trusted computation, as marked in `status.json`. Nothing proved here decides halting.

## Evidence and how to reproduce

```sh
./tmrun 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF 1000000000 records 100000      # tapes at each new cell
./tokrun 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF 1000000000 a=10,b=110 L 100000 # the tape as words at the left end (R for the right)
python3 -m bbtools.ctl 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF 5                # (from tools/py) the closed language and its halts
```

## For later

As for the twin: the rule of one wall visit on the block list.

## First look

Growth class **power/sqrt** (left: sqrt, exponent 0.506; right: power,
exponent 0.15). After 1,000,000,000 steps: 32,838 cells visited (23,688 left of the
start, 394 right), 25,123 ones.

- left, step 939,617,740: `B>0 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 `
- left, step 991,180,601: `E>0 1^2 0 1 0^2 1^2 0 1^2 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 0 1 0 1^2 0 1 0 1 `
- right, step 759,411,477: `1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 `
- right, step 945,073,674: `1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 `

## Accelerated run (13 November 2026)

Observed, not proved: the accelerated simulator `rsim.py` ran 8.29x10^13 steps from blank tape without reaching a halting transition. Its tape, state and head position were equal to those of a plain C simulator at 6 checkpoints, the last at 1.01x10^10 steps. Of these steps, the part after the last checkpoint rests on the simulator alone, including 7,944 trip-level jumps: a jump applies many identical round trips at once after seeing the same tape shape recur with constant count changes, which is validated against direct simulation but not proved.

```sh
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF 400
```

## PR 93's engine (22 November 2026)

**The table is PR 93's, with the halt moved.** Mirrored and with the states renamed (A→C, B→D, C→E, D→A, E→B, F→F) this
machine is `1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF` started in C. DeepMind's busycoq PR 93 proves that
1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD--- halts by running a verified fast engine on its source table
T3 = `1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB---`, started in C as well. The two tables differ in two places:

- T3's E and F have the same row (`0LB0LF`) except F1, where T3 halts. Here they are one state F, so where T3 halts
  this machine does what T3's E1 does (`0LF`) and goes on. Call T3 with F1 := 0LF the table W.
- T3's D0 is `1RA`. Here D0 = `1LE` and E0 = `0RA`: when the cell beyond holds 0, the three steps end exactly where
  T3's one step ends (A reads the 1 just written and moves on with `1RA`); when it holds 1, E1 halts. This is the only
  halt.

So this machine halts iff W's run from C ever has D reading 0 next to a 1 (in this machine's own orientation: B reading 0
with a 1 to its right). `lean/Detour.lean` proves the two cases (`detour`, `detour_halt`), kernel.

**Every rule of PR 93's engine is a rule of this machine.** `lean/PR93Rules.lean` (generated by `py/pr93rules.py`,
kernel) proves 44 theorems: PR 93's 21 basic macro rules (`rule_right`, `rule_left`, …, `rule_pairR`), the 5 rules at the
blank end (`rule_zeroL_*`), the 8 rules of the `DefWord` words (`def_*`) and the two fast right sweeps
(`rule_mr_a0_*`), each in this machine's orientation, for every count and every tape around (some split into the cases
count = 0 and count ≥ 1). They hold because none of their runs meets the detour's halting case; `py/rulecheck.py`
checks the same for the engine's shift scans (`scanR`, `scanB`, `scanC`, …) and for each rule with small counts. So a
fast step of the engine never hides a halt: a halt can only come in one of its raw single steps.

**The run (trusted).** `engine/build.sh` extracts PR 93's engine to OCaml with only the source table changed to W (the
engine's rules are rules of T3 that never reach F1, so they are rules of W). `engine/watch` runs it from C and tests at
every fast-step boundary whether the next steps reach the halting pattern (it looks ahead through B and C, so it can
over-report but not miss one):

- no halt in the first 7,889,000 fast steps, at the end of which the tape holds about 2^2764 cells;
- at fast step 2,452,241, on a tape of about 2^1400 cells, W is in F reading 1 (`engine/f1`): the configuration where
  PR 93's machine halts. This machine goes on there;
- `engine/validate` agrees with direct simulation of W through fast step 1,331 (3·10^11 steps), and in its first
  3.6·10^9 steps all 453,682,544 steps of D reading 0 have 0 next to them;
- in samples every 1,000th fast step, the longest run of 0s between two 1s is 2. Runs of three or more 0s occur only
  for a few steps in the engine's raw stretches at irregular events (e.g. fast steps 27,454 to 27,893), and so far never
  with the 1 beyond them that the halt needs.

This is not a proof either way: PR 93's soundness proof is for T3, and the run would have to go on forever. What would
decide the machine is an argument that the raw stretches never line up three 0s and a 1 in front of B.

## The raw steps, classified (22 November 2026)

PR 93's macro rules never take the halting route (`lean/PR93Rules.lean`, `py/rulecheck.py`), so a halt could only
come in one of the engine's unbatched steps. `engine/rawlog.ml` logs every one of them, groups consecutive ones into
*stretches*, and records the cells around each step that reads 0 on the way to the halt.

**The route into the halt** (`lean/HaltRoute.lean`, kernel). Walking back through this machine's table, the four steps
before any halt are forced: C reads 1, so B read 0 with a 1 beyond; B came from A0 (E1 would leave a 0 under C), so A
read 0; A came from E0, so E read `0 0 0 1` (`pre_halt`); and E came from A1 or F0, moving right (D0 writes a 1 beside
it) (`pre_halt_from`). So a halt needs three blank cells and then a 1 in front of E moving right. In the engine's
table W (mirrored, with the detour folded into D0 = `1RA`) this is B moving left onto 0 with `0 0 1` beyond it, then C
reading 0, then D reading 0 with a 1 beside it.

**The run (trusted).** From blank tape through fast step 30,442,000 (and, from the 30.4M checkpoint, on to 47,000,000)
the engine makes 65 raw stretches in the first run, every one of nine shapes (letters are W's, `>`/`<` the side the head
reads, the digit the cell read; `^n` a run of n equal steps):

| shape | times to 30.4M | steps |
|---|---|---|
| S0 | 1 (the start) | `C>0 D<0 A>1 A>0 B>0 C<1` |
| S1 | 16 | MR → `B>1 D>0 A>0^2 B>1 D>0 A>1^n A>0 B>0 C<1 B<1` → ML |
| S2 | 10 | ML → `D>1 E<0 B<1 D>0 A>0 B>1 D>1 E<0 B<1 D>0 A>0 B>0 C<1 B<1` → ML |
| S3 | 1 | MR → `B>1 D>0 A>0^3 B>1 D>1 E<0 B<1 D>0 A>0 B>0 C<1 B<1` → ML |
| S4 | 16 | ML → `D>1 E<0 B<1 D>0 A>0^2 B>1 D>1 E<0 B<1 D>0 A>0 B>0 C<1 B<1` → ML |
| S5 | 9 | ML → `C<0 D<1 E<1 F<1 F<0 B<1 D>0 A>0 B>0 C<1 B<1` → ML |
| S6 | 9 | MR → `B>1 D>0 A>0 B>1 D>0 A>1^n A>0 B>0 C<1 B<1` → ML |
| S7 | 1 | MR → `B>1 D>0 A>0^2 B>1 D>0 A>1 A>0 B>0 C<1 B<1` → ML |
| S8 | 2 | MR → `B>1 D>0 A>0 B>1 D>1 E<0 B<1 D>0 A>0 B>0 C<1 B<1` → ML |

(`A>0^k` is the engine's A0 shift scan, checked by `py/rulecheck.py`.) They come in clusters (at the two starts inspected, fast steps 27,452 and 300,971, the
engine's left side is a few words, then blank): S1 or S6 carries A rightward across a long block of 1s, one cell at a time (n = 419, 4,763, 7,213, …, 23,918: a
block the engine does not batch, which then sits on the left side), and S2/S4 turn the head back. The run from the
checkpoint shows no shape outside this list.

**Why none of them can halt.**

- Every D step that reads 0 in a raw stretch (119 of them to 30.4M) comes right after B reads 1, and B1 = `0RD` writes a
  0 on the cell beside D. That is the cell the halt needs to hold a 1, so these steps are safe whatever the tape holds.
- Every B step that reads 0 moving right (`B>0`) comes right after A0 = `1RB`, which leaves a 1 beside it, so C reads 1
  and turns back (`C<1`).
- The only raw step on the leftward route is S5's `C<0`, the event where PR 93's own machine halts (`F<1` a few steps
  later, its F1). It occurs 9 times to 30.4M (fast steps 2,452,238, 5,048,935, 5,433,032, …, 26,817,344), always with
  the same cells beyond it, `1 1 1 0`: the cell after the two 0s is a 1, so D reads 1 and the route stops one 0 short.
  In this machine's orientation: E moving right meets `0 0 1`, where a halt needs `0 0 0 1`.

So no raw step through 47,000,000 fast steps comes near a halt except the F1 event, which misses it by one cell every
time. What is left to prove is that the F1 event always has the same left-end context (`1 1 1 0` beyond its `0`) and
that no new raw shape appears: both are statements about the few words next to the cell read during these clusters, not
about the D-list, so they may be reachable with the cluster structure above. This is a classification of one long run,
not a proof.

```sh
sh engine/build.sh /path/to/busycoq && ulimit -s unlimited && engine/out/rawlog C 30442000 - ck.bin   # prints NEW/STRETCH lines and a summary
```

## Pages

- [`pages/holdouts/1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF/explainer.html`](../../pages/holdouts/1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF/explainer.html)
- [`pages/holdouts/1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF/proof-status.html`](../../pages/holdouts/1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF`](../1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F; it is this table started in state B
- [`1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF`](../1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF/README.md): rename A→C, B→D, C→E, D→A, E→B, F→F and exchange left and right; it is this table started in state D, in a mirror
- [`1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF`](../1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF/README.md): rename A→B, B→C, C→D, D→E, E→A, F→F; it is this table started in state E

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---`](../1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---/README.md): 8,004,077 configurations, the last at step 10,000,000 here and step 8,004,076 there
- [`1RB1RD_1LC0RE_1LD1LC_1RA0LE_1LC0RF_0RD---`](../1RB1RD_1LC0RE_1LD1LC_1RA0LE_1LC0RF_0RD---/README.md): 8,004,077 configurations, the last at step 10,000,000 here and step 8,004,076 there

<!-- end of related machines -->
