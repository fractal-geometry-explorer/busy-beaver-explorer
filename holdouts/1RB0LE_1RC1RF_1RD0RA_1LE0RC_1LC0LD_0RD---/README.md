# 1RB0LE_1RC1RF_1RD0RA_1LE0RC_1LC0LD_0RD---

bbchallenge id 4608. One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1RC | 1RF |
| C | 1RD | 0RA |
| D | 1LE | 0RC |
| E | 1LC | 0LD |
| F | 0RD | --- |

## What it does

**Sample point**: the head in C at the left end. With a = `1101010` and b = `10` the tape reads

    a^n  b^2 a b^10 (a b^2 a b^10)^m  a b^2 a b^34 a b^16 a b^32 a b^109 a b^320 a b^160 ... a b^538 a b^914 ... a b^k

(step 997,019,852: n = 3291). A pile of n blocks a, a list of numbers (runs of b between single a's, with pairs such
as 2/10, 16/32, 160/320, 538/914 repeated), and a final run b^k, the "fuse".

**Rule (observed)**: one sweep to the right end and back gives n -> n+1, k -> k-1 (width +5). The head shifts the
`10`s by one cell (C, D rightward; D, E leftward) and cycles the blocks a through `0011001`, `0101101`, `0010011`
(rules in `lean/Rules.lean`). When the fuse is used up the head stops returning to the left end and rebuilds the right
part as an expanding bouncer, with a much longer fuse: counting resumed at steps 8,170,570 (width 5,254) and
648,237,047 (width 49,385) after reorganizations that began at 75,408 and 19,673,806. A nested counter: each
reorganization takes much longer than the counting before it.

**Halting**: F on a 1 only; F from B on a 1, B (with a 1 ahead) from A on a 0, A only from C on a 1: it halts iff
`C> 1 0 1 1` occurs. In 10^9 steps A read a 0 5,815,845 times: followed by `1 0 1` 5,815,812 times, `1 0 0` 16, blank
17, never by `1 1`.

## Status

Open.

- **Lean, kernel** (`lean/Rules.lean`, from `py/rules.py`): `c_run`, `d_run`, `d_back`, `e_back`, `d_blocks`,
  `d_blocks_back`, `f_blocks`; `halt_shape` (`C> 1 0 1 1` reaches F on a 1 in 3 steps), `halt_after_shape`.
  `lean/Blank.lean`: no halt in 10^7 steps.
- **Trusted**: no halt in 10^9 steps; the near-miss count (`c/nbhd.c`).
- **Heuristic**: the counter form and the reorganization times (`c/samples.c`).

## Notes for later

- The reorganization is the whole difficulty: find the rule that turns the list of numbers into the next one (the
  repeated pairs suggest each level is built from the one below, as in a Collatz-like or Ackermann-like counter).
- A natural invariant to try: every `1` read by A after a 0 is followed by a 0 (ones stay isolated in the b-runs).

## Reproduce

```sh
gcc -O2 -o samples holdouts/1RB0LE_1RC1RF_1RD0RA_1LE0RC_1LC0LD_0RD---/c/samples.c && ./samples 1RB0LE_1RC1RF_1RD0RA_1LE0RC_1LC0LD_0RD--- 1000000000 C L 997000000 2
gcc -O2 -o nbhd holdouts/1RB0LE_1RC1RF_1RD0RA_1LE0RC_1LC0LD_0RD---/c/nbhd.c && ./nbhd 1RB0LE_1RC1RF_1RD0RA_1LE0RC_1LC0LD_0RD--- 1000000000 A 0
python3 holdouts/1RB0LE_1RC1RF_1RD0RA_1LE0RC_1LC0LD_0RD---/py/rules.py > holdouts/1RB0LE_1RC1RF_1RD0RA_1LE0RC_1LC0LD_0RD---/lean/Rules.lean
```

## Pages

- [`pages/holdouts/1RB0LE_1RC1RF_1RD0RA_1LE0RC_1LC0LD_0RD---/explainer.html`](../../pages/holdouts/1RB0LE_1RC1RF_1RD0RA_1LE0RC_1LC0LD_0RD---/explainer.html)
- [`pages/holdouts/1RB0LE_1RC1RF_1RD0RA_1LE0RC_1LC0LD_0RD---/proof-status.html`](../../pages/holdouts/1RB0LE_1RC1RF_1RD0RA_1LE0RC_1LC0LD_0RD---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1RC1RF_1RD0RA_1LE0RC_1LC0LD_0RD---/lean/check.sh
```
