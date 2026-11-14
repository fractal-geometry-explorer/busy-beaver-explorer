# 1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RA1LF_0LC---

bbchallenge id 86275, a six-state holdout of group G05 (growth class fixed/sqrt; in fact both ends grow, the right
end in bursts). **Open.** Sister of [`1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---`](../1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---/README.md), which differs only in E0 (1RA here, 1RD there):
the same particle system on a background of `10`s, with the same moving reflector Q, whose motion Lean (kernel)
proves exactly for every size, and the same stationary particles P; the collisions differ and are only observed.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RC |
| B | 1LC | 0LD |
| C | 1RA | 0LB |
| D | 1LE | 0RA |
| E | 1RA | 1LF |
| F | 0LC | --- |

## What it does


**Background.** Almost all of the tape is `1 0 1 0 ...`. A sweep shifts it by one cell: `A>1 0` becomes `0 1 A>`
(A1 = 0RC, C0 = 1RA), and leftwards B and C do the same, so the head crosses any amount of background at a steady
pace.

**Particles** (places where the pattern breaks):

* **Q**, the reflector: an extra `0` (short form) or an extra `1 1 0` (long form). The head bounces off it.
* **P** = `0 1 1 0 0`, stationary: the head crosses it and leaves it in place (observed).
* the **wall** `(1 0 0 1 1 0 0)^m` at the right end, which grows in bursts;
* the **left end** `1 1 0` (sometimes `(10)^3 1 1 0`), which grows two cells per bounce and now and then sends a
  new Q.

**One bounce** (exact). With the head in state A on the second cell,

    Q0 a c R = 1 A>1 0 (10)^a 0 (10)^c R          Q1 a c R = 1 A>1 0 (10)^a 1 1 0 (10)^c R

(blank on the left, anything on the right):

    Q0 a (c+2) R  ->  Q1 (a+2) c R        in 4a + 14 steps     (bounce0)
    Q1 a (c+1) R  ->  Q0 (a+2) (c+1) R    in 4a + 10 steps     (bounce1)
    Q0 a (c+1+2k) R  ->  Q0 (a+4k) (c+1) R   in 8ak + 16k^2 + 16k steps   (travel)

The head never reads `R`, and only states A to D occur. The bounces never use state E, which is why they are the same in both machines. Crossing n pairs takes about 16n² steps, hence the square
root growth.

**The long run** (observed). Reflectors leave the left end and travel right; meeting particles they pass, leave
particles behind or are absorbed. The right end grows in bursts to 7,627 cells by step 1.5·10⁸ and has not moved
since (up to 10¹⁰); the dense lattices next to the wall grow to the left one epoch at a time. At step 10¹⁰ the tape
is, with n for `(10)^n`,

    3 1^2 0 30149 0 36330 P 66 1^2 0 4530 P 2835 P 10283 P 2835 P 10283 P 2835 P 2215 1^2 0 2687 P 484
        P 297 P 185 ... P 260 P 17 P 33 ... P 3 P 11 ... (1 0 0 1 1 0 0)^m

910 particles P, mostly in lattices of alternating gaps (from the right) (3, 11) ×253, (17, 33) ×193, (297, 185) ×4,
(2835, 10283) ×3. `py/particles.png` shows the first 10⁹ steps.

**Where it can halt.** Only F reading 1; F is entered only from E reading 1, which never happens while a reflector
travels (the bounces use states A to D). A halt needs a collision configuration that has not occurred in 10¹⁰ steps.

## Status and evidence


* **Lean, kernel only.** `lean/Rules.lean` (written by `py/gen_rules.py` with `bbtools.symtm.prove`):
  `bounce0_cells`, `bounce1_cells`. `lean/Macro.lean`: `Q0`, `Q1`, `bounce0`, `bounce1`, `bounce2`, `travel`,
  `tcost_eq`. `lean/Reach.lean`: `reach_Q0` (blank tape reaches `Q0 4 26 R1`, `R1 = 0 1 1 0 0 1 1 0 0 1 1 0 0 1`,
  after 1,819 steps), `reach_travel` (`Q0 52 2 R1` at 4,699), `reach_P` (`Q1 54 0 R1` at 4,921, Q next to the first P).
  `lean/Blank.lean` (generated): no halt in 10⁷ steps.
* **Computed (trusted).** `py/snap.c`: no halt in 10¹⁰ steps (56 s); final tape spans −250,050 … 7,627; the
  particle form above (`py/tokens.py`).
* **Heuristic.** The collision rules and the epoch structure, from the simulation.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RA1LF_0LC---/lean/check.sh
python3 holdouts/1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RA1LF_0LC---/py/gen_rules.py
gcc -O2 -o snap holdouts/1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RA1LF_0LC---/py/snap.c
./snap 1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RA1LF_0LC--- 10000000000 L 1 9998000000 | tail -1 | python3 holdouts/1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RA1LF_0LC---/py/tokens.py
./snap 1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RA1LF_0LC--- 1000000000 L 40 > img.txt && python3 holdouts/1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RA1LF_0LC---/py/particles_img.py img.txt particles.png -81000 7700 640
```

## Accelerated run (13 November 2026)

Observed, not proved: the accelerated simulator `rsim.py` ran 1.21x10^13 steps from blank tape without reaching a halting transition. Its tape, state and head position were equal to those of a plain C simulator at 6 checkpoints, the last at 1.96x10^10 steps. Of these steps, the part after the last checkpoint rests on the simulator alone, including 874 trip-level jumps: a jump applies many identical round trips at once after seeing the same tape shape recur with constant count changes, which is validated against direct simulation but not proved.

```sh
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RA1LF_0LC--- 400
```

## Pages

- [`pages/holdouts/1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RA1LF_0LC---/explainer.html`](../../pages/holdouts/1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RA1LF_0LC---/explainer.html)
- [`pages/holdouts/1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RA1LF_0LC---/proof-status.html`](../../pages/holdouts/1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RA1LF_0LC---/proof-status.html)

## For later

The motion of Q is closed; the missing pieces are the collision rules. Next steps: prove with `symtm` the events
"Q meets P" (for all gap sizes), "Q meets the wall" and "the left end emits Q", define a macro machine on the list of
gaps between particles, prove it sound like `travel`, and run it far past 10¹⁰ steps; then look for an invariant of
the lattices that keeps the F1 configuration out of every collision.

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---`](../1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---/README.md): rename A→B, B→C, C→A, D→D, E→E, F→F; it is this table started in state C
- [`1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LC1RF_0RB---`](../1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LC1RF_0RB---/README.md): rename A→C, B→A, C→B, D→D, E→E, F→F and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
