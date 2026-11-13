# 1RB0RE_1LC0LE_---1LD_1LE1LB_1RA0LF_0RD1LA

bbchallenge id 39050. A register machine on the tape: blocks of 7-cell words w = 1111110 and long runs of 1s, which phases of bounces at the left end drain one into the other at fixed rates (one w becomes fifteen 1s), with new registers appearing as the tape grows.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RE |
| B | 1LC | 0LE |
| C | --- | 1LD |
| D | 1LE | 1LB |
| E | 1RA | 0LF |
| F | 0RD | 1LA |

## What it does

Words `w = 1111110`, `x = 111110`. The tape is a few registers: blocks `w^a` and runs `1^b`, separated by `0 0`, plus
a nearly fixed right end. Step 2,001,556 (head at the left end):

    [A1] 1 0 0 w x w^103 0 0 1^424 w^2 x^105 0 0 1^2 w x^2 0 0 1^10

**Phases** (observed, sampled with A at the left end):

- drain: `w x w^a 0 0 1^b R -> w x w^(a-1) 0 0 1^(b+15) R` every 3 visits (+8 cells);
  e.g. a = 103, 102, 101 with b = 424, 439, 454 at steps 2,001,556, 2,016,698, 2,031,696;
- build: `w x w^a 1111 0 w^c 0 0 1^b R -> w x w^(a+2) 1111 0 w^(c-3) 0 0 1^(b+15) R`.

Later tapes hold more registers, e.g. step 1,366,620,342 (55,573 cells):
`1 0^4 x^2 w^19 1^4 0 1^4 0 w^2279 0^2 1^11707 w x w^2311 0^2 1^11514 w^2 1^9 w^2 0^2 1^5`.

**Proved** (`lean/Rules.lean`): the eight shift rules across rotations of `w` and `x` (A, E right; B, C, D, E left).

## Halting

Only C0 halts; C is entered only from B0 (1LC): halts iff `0 B> 0`. Not seen inside a phase; the phase changes are
where it could happen.

- CTL K = 3..6: halts remain; n-gram CPS 3..7 fails; no invariant mod 2..12. No halt in 3·10^9 steps.

## Notes for later

- Prove the drain and build rounds as macro rules (three visits per word).
- Derive the phase-change map on (a, b, c, ...) and look for a Collatz-like rule.

## Pages

- [`pages/holdouts/1RB0RE_1LC0LE_---1LD_1LE1LB_1RA0LF_0RD1LA/explainer.html`](../../pages/holdouts/1RB0RE_1LC0LE_---1LD_1LE1LB_1RA0LF_0RD1LA/explainer.html)
- [`pages/holdouts/1RB0RE_1LC0LE_---1LD_1LE1LB_1RA0LF_0RD1LA/proof-status.html`](../../pages/holdouts/1RB0RE_1LC0LE_---1LD_1LE1LB_1RA0LF_0RD1LA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RE_1LC0LE_---1LD_1LE1LB_1RA0LF_0RD1LA/lean/check.sh
```
