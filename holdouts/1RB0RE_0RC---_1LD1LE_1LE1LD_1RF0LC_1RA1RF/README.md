# 1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF

bbchallenge id 75625. A binary word written in 4-cell letters 1110 and 1111; every leftward sweep replaces it by its running parity (XOR from the right), so the space-time diagram is Pascal's triangle mod 2 (Sierpinski triangles), in epochs that each grow the tape by about 1.75.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RE |
| B | 0RC | --- |
| C | 1LD | 1LE |
| D | 1LE | 1LD |
| E | 1RF | 0LC |
| F | 1RA | 1RF |

## What it does

Letters `u = 1110`, `v = 1111`. Between sweeps the tape is a word in `u` and `v` (blocks `1^(4k+3) 0`) plus a short
fixed end on the right. Step 2,003,981:

    u^3 v u v^2 u v u v u^3 v^2 u v u v u v^2 u^2 v^3 u v^2 u v^3 u v u^3 ...   (about 650 letters)

**Leftward sweep = running parity** (proved, `lean/Rules.lean`). The head is in D (even) or C (odd) on the last cell
of a word `111x`:

| state | letter | writes | next |
|---|---|---|---|
| D | u = 1110 | 0101 | C |
| D | v = 1111 | 1111 | D |
| C | u | 1111 | D |
| C | v | 0101 | C |

so behind the head is the running XOR from the right (u = 1), written as 1111 (even) / 0101 (odd). Iterating the
running XOR gives Pascal's triangle mod 2: the Sierpinski triangles of the space-time diagram.

**Epochs** (observed, `c/epochs.c`). The head bounces between the left end and an inner wall that moves left; the
zone between them is rewritten every bounce, the tape right of the wall is frozen; when the zone closes, a full
crossing starts a new epoch.

| step | left end | right end |
|---:|---:|---:|
| 47,799 | 374 | 47 |
| 145,962 | 703 | 58 |
| 487,979 | 1,319 | 69 |
| 1,427,948 | 2,265 | 80 |
| 4,277,179 | 4,020 | 91 |
| 13,419,889 | 7,237 | 98 |
| 40,483,837 | 12,641 | 109 |
| 124,076,294 | 22,085 | 112 |
| 383,276,545 | 38,918 | 115 |
| 1,162,585,978 | 68,091 | 130 |

## Twin

`1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF` has identical configurations at 12 of the 13 epoch starts up to
1.7·10^9 steps (about 1.5 times later); see its folder.

## The tape as a list of blocks (F11, 13 November 2026)

Read the tape as blocks of 1s separated by single 0s. Every meeting of the head with a block or a separator is one of
the rules of `lean/Blocks.lean` (kernel; written by `py/blocks_rules.py`):

| going | situation | what happens | rule |
|---|---|---|---|
| right, F | a block | crossed | `f_block` |
| right, F | separator, then a block of one cell | separator filled, the cell erased, the next separator filled, F goes on: the blocks on both sides gain a cell each | `f_single` |
| right, F | separator, then a block of two or more | **turn**: the block on the left gains two cells, the block on the right loses two, the head leaves in D | `f_turn` |
| right, F | `0 0 0 1` | filled | `f_three_zeros` |
| right, F | `0 0 0 0` (right end) | writes `1011`, leaves in E | `f_end` |
| right, F | `0 0 1` | **halt** | `halt_F` |
| left, D | a block | crossed and kept; the separator after it is filled and the next block is entered in E | `d_block`, `d_sep` |
| left, E | a block | every second cell erased (the block becomes blocks of one cell); if its length is odd the next separator is filled and the next block is entered in D, if even E reaches the separator and turns right | `e_pairs`, `e_last`, `c_sep`, `c_last`, `e_turn` |

So a leftward pass keeps and breaks up blocks in turn (that is the running parity of `lean/Rules.lean`, a block
`1^(4k+3) 0` being the word `v^k u`), and a rightward pass merges what was broken, until it meets a block of two
or more cells and turns there.

`python3 py/blocks.py 100000 4016 70` prints the block lists at every turn. What they show (observed, one epoch
followed turn by turn, steps 4,104 to 7,890):

- **Growing phase.** The head bounces between the left end of the tape and a turning place that moves right, 2 to 20
  cells per bounce, eating the blocks beyond it two cells at a time (27, 20, 24, 28, 32, 49, 53, 73, ... 155 cells
  from the left end). At each turn on the right the zone is a list of blocks `1^(4k+3)` (the last one a cell
  longer); at each turn on the left it is blocks `1^(4k+1)` separated by odd numbers of one-cell blocks.
- **Crossing phase.** When the turning place reaches the right end of the tape, the head crosses back to the left end
  in short bounces (8 to 28 cells wide), leaving behind it blocks of 3 and pairs `1, 5` (the 4-cell words `1110` and
  `1011`), which the next growing phase eats.

## Halting

Only B1 halts; B is entered only from A0 and A only from F0 (`1RA`). So the machine halts exactly on `F> 0 0 1`:
`halt_F` (`lean/Blocks.lean`) and, for the converse, `halt_route` (`lean/Route.lean`: two steps before any halt the
machine is in F on `0 0 1`). An earlier version of this page said `F> 1 0 1`; that was wrong (F on a 1 stays in F).

One way to put `0 0 1` on the tape is a turn at a block of exactly two cells that has another block after it
(`turn_two`): the turn erases the block and leaves its separator next to the next one. In the run from blank tape
(`c/turns.c`, 10^10 steps, 139,833 turns of F):

- every turn was at a block of odd length (3: 36,463 times; 5: 46,436; 7: 19,254; 9: 20,280; ...), except 22 turns
  at a block of exactly two cells, and each of those was the last block of the tape, with blank tape after it;
- F met two 0s in a row 42 times, each time at the right end of the tape with only blank cells beyond.

So up to 10^10 steps the question is decided at the right end only, about twice per epoch. This is an observation.
What would make it a proof is an invariant that keeps every block that is turned at odd, away from the right end, and
a description of the right end; neither is proved.

Regular-language deciders tried here (all fail, i.e. their closed sets contain a halting configuration; none of this
says anything about halting): see "Deciders tried" below.

- No halt in 10^10 steps (`c/turns.c`).

## Notes for later

- The turning places and the left end are now rules on blocks; the missing piece is the format of the tape at the
  start of an epoch (which blocks the crossing phase can leave) and what the right end does with it.
- The three other machines with this table (see Related machines) obey the same block rules after renaming states
  and mirroring; their runs are different.

## Pages

- [`pages/holdouts/1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/explainer.html`](../../pages/holdouts/1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/explainer.html)
- [`pages/holdouts/1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/proof-status.html`](../../pages/holdouts/1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**[`1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF`](../1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF/README.md) is a slowed-down copy of this machine (observed, not proved).** Read that machine's states A as A, B as B, D as C, E as E, F as F of this machine. Then 4,995,966 of its first 10^7 configurations (tape, head position and state) are configurations of this machine, in the same order. The last one is step 9,999,982 there and step 6,664,008 here, so it takes about 1.5 times as many steps. The tables are not renamings of each other. Lean proves (`lean/Twin.lean` in the other machine's folder, `sim_or_break`, `not_halts_of_noBreak`) that each step of the faster machine is matched by one or three steps of the slower one up to the first break, a configuration where the paired states act differently, and that neither machine halts if no break ever comes. A halt of either machine is itself a break, and the halting transitions of the two do not correspond, so the two are not known to halt together.

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB`](../1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB/README.md): rename A→D, B→E, C→F, D→A, E→B, F→C and exchange left and right; it is this table started in state D, in a mirror
- [`1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF`](../1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/README.md): rename A→C, B→D, C→E, D→F, E→A, F→B; it is this table started in state E
- [`1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---`](../1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---/README.md): rename A→E, B→F, C→A, D→B, E→C, F→D and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
