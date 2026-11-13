# 1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---

bbchallenge id 54407, a six-state holdout of group G05 (growth class fixed/sqrt). **Open.** The machine is a
particle system on a background of `10`s: the head bounces between the left end of the tape and a moving reflector
Q, pushing it one pair to the right every two bounces; stationary particles P pile up in lattices; a wall at the
right end grows in bursts. Lean (kernel) proves the motion of Q exactly, for every size, and that the run from blank
tape reaches this picture; the collisions are only observed.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RC |
| B | 1LC | 0LD |
| C | 1RA | 0LB |
| D | 1LE | 0RA |
| E | 1RD | 1LF |
| F | 0LC | --- |

Its sister [`1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RA1LF_0LC---`](../1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RA1LF_0LC---/README.md)
differs only in E0 (1RA there, 1RD here); the background, the particles and the bounce rules are the same.

## What it does

**Background.** Almost all of the tape is `1 0 1 0 ...`. A sweep shifts it by one cell: `A>1 0` becomes `0 1 A>`
(A1 = 0RC, C0 = 1RA), and leftwards B and C do the same, so the head crosses any amount of background at a steady
pace.

**Particles** (places where the pattern breaks):

* **Q**, the reflector: an extra `0` (short form) or an extra `1 1 0` (long form). The head bounces off it.
* **P** = `0 1 1 0 0`, stationary: the head crosses it and leaves it in place (observed).
* the **wall** `(1 0 0 1 1 0 0)^m` at the right end, which grows three cells per bounce in bursts;
* the **left end** `1 1 0` (sometimes `(10)^3 1 1 0`), which grows two cells per bounce and now and then sends a
  new Q.

**One bounce** (exact). With the head in state A on the second cell,

    Q0 a c R = 1 A>1 0 (10)^a 0 (10)^c R          Q1 a c R = 1 A>1 0 (10)^a 1 1 0 (10)^c R

(blank on the left, anything on the right):

    Q0 a (c+2) R  ->  Q1 (a+2) c R        in 4a + 14 steps     (bounce0)
    Q1 a (c+1) R  ->  Q0 (a+2) (c+1) R    in 4a + 10 steps     (bounce1)
    Q0 a (c+1+2k) R  ->  Q0 (a+4k) (c+1) R   in 8ak + 16k^2 + 16k steps   (travel)

The head never reads `R`, and only states A to D occur. Crossing n pairs takes about 16n² steps, hence the square
root growth.

**The long run** (observed). A reflector leaves the left end and travels right. Meeting a P, it passes, leaves a
particle behind or is absorbed (then the left end sends a new one); reaching the wall, it makes the right end grow
three cells per bounce for a while (bursts at steps 1,366, 96,934, 473,188, 1,276,984 and 1.2·10⁹; the right end
at 14, 80, 262, 562, 922 between them). At step 10¹⁰ the tape is, with n for `(10)^n`,

    3 1^2 0 1513 P 40809 0 12470 P 733 1^2 0 4183 P 7557 P 430 P 1385 P 2985 P ... P 555 P 899 P ...
        ... P 185 P 297 P ... P 59 P 99 ... (1 0 0 1 1 0 0)^m

293 particles P, mostly in lattices of alternating gaps (from the right) (3, 11) ×52, (9, 41) ×18, (59, 99) ×37,
(185, 297) ×27, (555, 899) ×6, (1385, 2985) ×3, each built in one epoch and more widely spaced than the one before. `py/particles.png` shows the first 10⁹ steps (every 40th
left turn; black = broken pattern).

**Where it can halt.** Only F reading 1; F is entered only from E reading 1, which never happens while a reflector
travels. A halt needs a collision configuration that has not occurred in 10¹⁰ steps.

## Status and evidence

* **Lean, kernel only.** `lean/Rules.lean` (written by `py/gen_rules.py` with `bbtools.symtm.prove`):
  `bounce0_cells`, `bounce1_cells`. `lean/Macro.lean`: `Q0`, `Q1`, `bounce0`, `bounce1`, `bounce2`, `travel`,
  `tcost_eq`. `lean/Reach.lean`: `reach_Q0` (blank tape reaches `Q0 3 10 R0`, `R0 = 0 1 1 0 0 1 1`, after 397
  steps), `reach_travel` (`Q0 19 2 R0` at 813), `reach_P` (`Q1 21 0 R0` at 903, Q next to the first P).
  `lean/Blank.lean` (generated): no halt in 10⁷ steps.
* **Computed (trusted).** `py/snap.c`: no halt in 10¹⁰ steps (43 s); final tape spans −256,550 … 30,857; the
  particle form above (`py/tokens.py`).
* **Heuristic.** The collision rules and the epoch structure, from the simulation.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---/lean/check.sh
python3 holdouts/1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---/py/gen_rules.py
gcc -O2 -o snap holdouts/1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---/py/snap.c
./snap 1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC--- 10000000000 L 1 9998000000 | tail -1 | python3 holdouts/1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---/py/tokens.py
./snap 1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC--- 1000000000 L 40 > img.txt && python3 holdouts/1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---/py/particles_img.py img.txt particles.png -61000 1000 640
```

## Pages

- [`pages/holdouts/1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---/explainer.html`](../../pages/holdouts/1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---/explainer.html)
- [`pages/holdouts/1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---/proof-status.html`](../../pages/holdouts/1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---/proof-status.html)

## For later

The motion of Q is closed; the missing pieces are the collision rules. Next steps: prove with `symtm` the events
"Q meets P" (for all gap sizes), "Q meets the wall" and "the left end emits Q", define a macro machine on the list of
gaps between particles, prove it sound like `travel`, and run it far past 10¹⁰ steps; then look for an invariant of
the lattices that keeps the F1 configuration out of every collision.

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---`](../1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---/README.md): rename A→B, B→C, C→A, D→D, E→E, F→F; it is this table started in state C
- [`1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---`](../1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---/README.md): rename A→C, B→D, C→E, D→A, E→B, F→F and exchange left and right; it is this table started in state D, in a mirror
- [`1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LD1RF_0RB---`](../1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LD1RF_0RB---/README.md): rename A→C, B→A, C→B, D→D, E→E, F→F and exchange left and right; it is this table started in state B, in a mirror
- [`1RB1LC_1LA0RE_0LD---_1RE0LF_1RF0RD_1LD0LB`](../1RB1LC_1LA0RE_0LD---_1RE0LF_1RF0RD_1LD0LB/README.md): rename A→E, B→F, C→D, D→B, E→A, F→C; it is this table started in state E

<!-- end of related machines -->
