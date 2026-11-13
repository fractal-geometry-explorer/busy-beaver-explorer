# 1RB0RC_1RC1RA_1LD0RA_0LE1RA_---1LF_1RB0LF

bbchallenge id 21851. One of the six-state holdouts whose halting from blank tape is open; analyzed by hand (group G02). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RC |
| B | 1RC | 1RA |
| C | 1LD | 0RA |
| D | 0LE | 1RA |
| E | --- | 1LF |
| F | 1RB | 0LF |

## What it does

F sweeps left erasing 1s and turns at a 0; A, B and C sweep right. Each time F reaches a new cell on the left, the
tape is a short prefix from a cycle of about ten, a middle of identical blocks `1 0 1 0^8`, and a right end (here with
`a = 10`, `b = 110`):

    step 19,164:   0000000010100001011011010000001010000 (1010^8)^16 ... 0a0aa0abbba0aa000aba0aa00000ab1
    step 356,532:  0000101... (1010^8)^104 ... 0a00000aa0aa000aa0aa0aa0aa000aba0aa000abbbbbbbbba000ab1

The middle gains about one block per cycle of the left end; the right end's runs of b grow and collapse with no
pattern decoded. Width grows linearly with the sweeps, so time is about quadratic in the width (width 5,692 at step
6,664,000).

## Status

Open. The only halt is E reading a 0, after D reads a 0.

- Lean, kernel: C going right over `1^(2n+2) 0` halts, for every n and any surrounding tape (`halts_C_even`); shift
  rules for C and A over `(11)^n` (`lean/Rules.lean`); halting configurations, 10^4 steps (`lean/Blank.lean`).
  `native_decide`: 10^7 steps.
- Computed: no halt in 10^10 steps (`tools/c/tmrun.c`, 176,203 ones); in 10^9 steps D read a 0 about 7·10^6 times and
  E always read a 1 next; `bbtools.ctl` K = 2..7 allows a halt.

## Notes for later

- Decode the right end (the runs of `110` between `10`s) at the sweep turns; then check which configurations put C on
  an even run of 1s before a 0, or D on a 0 after another 0.

## Pages

- [`pages/holdouts/1RB0RC_1RC1RA_1LD0RA_0LE1RA_---1LF_1RB0LF/explainer.html`](../../pages/holdouts/1RB0RC_1RC1RA_1LD0RA_0LE1RA_---1LF_1RB0LF/explainer.html)
- [`pages/holdouts/1RB0RC_1RC1RA_1LD0RA_0LE1RA_---1LF_1RB0LF/proof-status.html`](../../pages/holdouts/1RB0RC_1RC1RA_1LD0RA_0LE1RA_---1LF_1RB0LF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RC_1RC1RA_1LD0RA_0LE1RA_---1LF_1RB0LF/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF`](../1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF/README.md): rename A→D, B→A, C→B, D→C, E→E, F→F; it is this table started in state B

<!-- end of related machines -->
