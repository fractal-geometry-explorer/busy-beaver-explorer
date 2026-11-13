# 1RB0RD_1RC0RA_0LA0LE_1LC1RF_1LA1LC_0RB---

bbchallenge id 16554. A body of (10)^n that is repeatedly packed into (1100)^m and unpacked again by sweeps, in epochs that each grow the tape by a factor about 5/3, with a small irregular region at the left end that grows only in some epochs.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RD |
| B | 1RC | 0RA |
| C | 0LA | 0LE |
| D | 1LC | 1RF |
| E | 1LA | 1LC |
| F | 0RB | --- |

## What it does

Words: `a = 10`, `b = 1100`. The tape is a small irregular region at the left end (a few hundred cells, the side that
grows like a logarithm) followed by a long body made of `a` and `b` (the side that grows like a square root). A real
tape, step 1,001,933:

    a 0 b^173 1 1 [A0] 0 a^5 0 a^2 1 a^519 1

**Moves across the body** (proved, `lean/Rules.lean`): `B> (10)^n -> (01)^n B>` (2n steps), `A> (01)^n -> (10)^n A>`
(2n steps), and `(1010)^n C> 0 1 -> C> 0 1 (1010)^n` (10n steps: C carries a `0 1` defect left without changing the
body).

**Epochs** (observed). An epoch starts with an active zone of `(10)^n` at the right end; the head bounces in it, each
bounce adds 3 cells at the right end and the zone's left edge moves left into the packed `(1100)^m` region. When the
zone reaches the left region the head makes full-width sweeps that pack `(10)(10)` into `1100` going right and unpack
going left; the left region is rewritten; a new zone starts. Epoch starts (a sweep over 80% of the tape,
`c/epochs.c`) to 10^10 steps:

| step | right end | left end |
|---:|---:|---:|
| 100,618 | 284 | 141 |
| 213,384 | 556 | 152 |
| 514,417 | 1,017 | 164 |
| 1,329,037 | 1,793 | 170 |
| 3,738,738 | 3,126 | 199 |
| 19,372,038 | 4,946 | 283 |
| 32,388,399 | 7,969 | 283 |
| 70,752,889 | 13,277 | 283 |
| 172,844,740 | 22,192 | 283 |
| 454,817,413 | 37,035 | 283 |
| 1,259,326,927 | 61,817 | 386 |
| 6,311,514,639 | 94,515 | 438 |

Regular epochs: right end x1.67, time x2.7 (about (5/3)^2). The irregular ones (time x5) are where the left end moved.

## Halting

Only F1 halts; F is entered only from D1, D only from A1, so the machine halts iff some time `A> 1 1 1`. The body
never contains `111`; only the left region and the short debris during packing sweeps can. The halting question is
therefore about the left region, rewritten once every few epochs; its rule was not found.

- CTL (`bbtools.ctl`), K = 3, 4, 5, 6: no closed set without halts. n-gram CPS widths 3-7 (with -H, -U): fails.
- No halt in 10^10 steps (C, `c/epochs.c`).

## Notes for later

- Find the rule of the left region between epochs (dump it at each epoch start: `c/epochs.c` gives the times).
- Prove the zone bounce as a macro rule (the turn at the right end and at the zone's left edge involve short
  irregular words; see the trace around step 1,980,000 in the packing sweep).

## Pages

- [`pages/holdouts/1RB0RD_1RC0RA_0LA0LE_1LC1RF_1LA1LC_0RB---/explainer.html`](../../pages/holdouts/1RB0RD_1RC0RA_0LA0LE_1LC1RF_1LA1LC_0RB---/explainer.html)
- [`pages/holdouts/1RB0RD_1RC0RA_0LA0LE_1LC1RF_1LA1LC_0RB---/proof-status.html`](../../pages/holdouts/1RB0RD_1RC0RA_0LA0LE_1LC1RF_1LA1LC_0RB---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RD_1RC0RA_0LA0LE_1LC1RF_1LA1LC_0RB---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RD_1LC0LE_1LD0LB_0RB0RA_1RD1LF_0LC---`](../1RB1RD_1LC0LE_1LD0LB_0RB0RA_1RD1LF_0LC---/README.md): rename A→B, B→C, C→D, D→E, E→A, F→F and exchange left and right; it is this table started in state E, in a mirror
- [`1RB0RC_0LC0LE_1RA0RD_1LB1RF_1LC1LB_0RA---`](../1RB0RC_0LC0LE_1RA0RD_1LB1RF_1LC1LB_0RA---/README.md): rename A→C, B→A, C→B, D→D, E→E, F→F; it is this table started in state B

<!-- end of related machines -->
