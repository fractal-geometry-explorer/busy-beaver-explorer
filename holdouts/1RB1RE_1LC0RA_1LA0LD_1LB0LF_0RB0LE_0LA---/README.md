# 1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---

bbchallenge id 48016. Open. **Exactly the mirror image of `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---` with states A
and D exchanged**: reflect that machine (L and R swapped) and rename A to D and D to A, and you get this machine's
table, transition for transition. So this run is that machine's table started in state D (instead of A) on a blank
tape, seen in a mirror. It is a different orbit of the same dynamics: a **nested crossing counter** whose tape is a
few long blocks of 3-cell words and a final block of a 9-cell word (here at the *left* end, `101101100` and its
rotations), changed by the same five kinds of phase (one period of four of them proved in Lean here, mirrored; the drain period is proved for the twin), with rounds
that multiply the tape by about 2.2. The exact accelerated simulator of the twin (`ACCEL_X=1`) follows it to
**1.06·10^300 steps** (401 drain phases) without a halt. See the twin's README for the round maps.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RE |
| B | 1LC | 0RA |
| C | 1LA | 0LD |
| D | 1LB | 0LF |
| E | 0RB | 0LE |
| F | 0LA | --- |

## The mirror

Twin `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---`: A 1RB 0RF, B 1RC 0LD, C 1RD 0RA, D 1LB 1LE, E 0LB 0RE, F 0RD ---.
Swap L/R and rename A<->D: D 1LB 0LF, B 1LC 0RA, C 1LA 0LD, A 1RB 1RE, E 0RB 0LE, F 0LA --- , which is this table.
Its start state A is the twin's D (`py/mirror.py` tries every renaming; this is the only match). The two runs need not
meet, but they use the same phase rules (mirrored).

## The tape as words

At the left end (state E): `0 0 0 (101101100)^p (101)^q ... (110)^t 1`, e.g. step 3,039,097,886:
`0 0 0 (101101100)^509 (101)^4551 (100)^856 (101)^5329 (110)^10179 1`. The final block is `(101101100)^p` at the left;
the long blocks of `101`, `100`, `110`, `001` are to its right.

## The phases

One period of each except drain, kernel (`lean/Phases.lean`, `PhasesFeed.lean`, from `py/phases.py`); the older `traverse` of `lean/Rules.lean` is
the crossing phase in another form.

| phase | per period | Lean |
|---|---|---|
| cross | the marker moves 6 words right through the last block, left (final) block +1 | `cross6` (also `traverse`) |
| drain | final block -11, a marker moves 18 words, a new block +36 | not in Lean here (see below) |
| double cross | two markers move 12 words, final block +1 | `cross12`, `cross12b` |
| absorb (right end) | right block +4, its neighbour -2 | `absorb2` |
| feed (right end) | a middle block -18, right block +30, final block +1 | `feed30` |

The drain period is stated in `py/phases.py` and holds symbolically (`accel.py`, `bbtools.symtm`), but its generated
Lean proof (16,000 steps, 3.7 MB) needs more than 9 GB of memory and was killed, so it is not in `check.sh`. The
mirror-image period is kernel-checked for the twin (`drain11` in its `lean/PhasesDrain.lean`).

## Exact simulation

`../1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---/py/accel.py` with `ACCEL_X=1` (a crossing of a long block is also an
event; this run has phases in which the head zig-zags inside the tape for a long time). Checked against direct
simulation (`check_accel.py`, `c/tapeat.c` there) after every jump up to 1.08·10^10 steps: 0 mismatches. From
blank tape it reaches 1.06·10^300 steps without a halt; the drain phases are in `py/rounds_1e300.log`
(`py/rounds.py` of the twin). Tape growth per drain phase 1.98 to 4.01 (median 2.23).

## Halting

The only halting transition is F on a 1; F is entered only from D on a 1 (D writes 0, moves left). In every phase
rule that cell is a 0.

## Status

Open. Kernel: halting configurations, 10,000 steps, five phase periods (`Phases.lean`, `PhasesFeed.lean`: cross6, cross12, cross12b, absorb2, feed30) and `traverse`
(`Rules.lean`). Native: 10^7 steps. Trusted: no halt in 10^10 steps (`c/ev.c`) and in 1.06·10^300 steps of the exact
accelerated simulation. The phase ends are from simulation only.

## For later

* One closure proof for the twin's table would cover both runs only if it covers all configurations both reach;
  see the twin's "For later".

## First look

Growth class **sqrt/sqrt** (left: sqrt, exponent 0.474; right: sqrt,
exponent 0.57). After 1,000,000,000 steps: 34,812 cells visited (9,917 left of the
start, 19,053 right), 19,072 ones.

- left, step 968,946,971: `E>0 0^2 1 0^2 1 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 `
- left, step 984,720,342: `A>0 1^2 0^2 1 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^2 0 1^2 0^2 1 0 1^`
- right, step 531,276,874: `1 0 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 `
- right, step 546,919,364: `1 0 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 0^2 1 0^2 1^2 0 1 `

## Pages

- [`pages/holdouts/1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---/explainer.html`](../../pages/holdouts/1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---/explainer.html)
- [`pages/holdouts/1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---/proof-status.html`](../../pages/holdouts/1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---/lean/check.sh     # about 90 s
python3 holdouts/1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---/py/phases.py      # regenerates lean/Phases.lean, lean/PhasesFeed.lean
python3 holdouts/1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---/py/mirror.py
ACCEL_X=1 python3 holdouts/1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---/py/rounds.py 1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA--- 1e300 > rounds.log
gcc -O2 -o /tmp/tapeat holdouts/1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---/c/tapeat.c
ACCEL_X=1 python3 holdouts/1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---/py/check_accel.py 1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA--- 2e10 /tmp/tapeat
gcc -O2 -o ev holdouts/1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---/c/ev.c && ./ev 1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA--- 2000000000 L E 1 100000 12 | awk 'NR%300==0'
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---`](../1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---/README.md): rename A→D, B→B, C→C, D→A, E→E, F→F and exchange left and right; it is this table started in state D, in a mirror

<!-- end of related machines -->
