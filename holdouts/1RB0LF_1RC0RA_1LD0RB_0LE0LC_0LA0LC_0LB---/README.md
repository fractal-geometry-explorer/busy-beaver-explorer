# 1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---

bbchallenge id 92633. One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 1RC | 0RA |
| C | 1LD | 0RB |
| D | 0LE | 0LC |
| E | 0LA | 0LC |
| F | 0LB | --- |

## What it does

**Tape**: a sea of `10` with single markers `100` / `1000`. **Sample point**: C on a 1 at the right end (once a
sweep). At step 974,444,280, as runs (`1x56` = (10)^56, `1/2` = 100, `1/3` = 1000):

    1 1/2x2 1x56 1/3 1x4 1/2 1x277 1/2 1x512 1/2 1x2 1/2 1x2877 1/3 1x26463 2/E

**Sweeps**: the head bounces over the whole tape; rightward A turns (01)^n into (10)^n and A/B cross the markers,
leftward C and D cross the sea (`lean/Rules.lean`). **Rule (observed)**: during a round the last two runs change
X -2, Y +3 each sweep (7.25·10^8 to 9.74·10^8: 8477, 18063 -> 2877, 26463). When X is used up the small runs on the
left are rewritten (52,4,293,497,17 -> 40,16,290,500,15 -> 56,4,277,512,2) and a longer round starts; rounds began
near steps 4.59·10^7, 1.01·10^8, 2.28·10^8, 5.11·10^8 with X = 5546, 8649, 12310, 18877.

**Halting**: F on a 1 is the only halt; F comes only from A on a 1, and A has a 1 on its left only when it came from
E on a 0. So it halts iff `1 1 E> 0` occurs (`halt_shape`). In 10^9 steps E read a 0 30,301 times, never with `1 1`
to its left.

## Status

Open.

- **Lean, kernel** (`lean/Rules.lean`, from `py/rules.py`): `a_run`, `b_run`, `a_run4`, `c_run`, `d_run`,
  `halt_shape`, `halt_after_shape`. `lean/Blank.lean`: no halt in 10^7 steps.
- **Trusted**: no halt in 10^9 steps; near-miss counts (`c/nbhd.c`).
- **Heuristic**: the round pattern (`c/tok.c`).

## Notes for later

- Find the end-of-round rule: how the small runs x0..x4 and the new X, Y follow from the old ones. Then prove the
  round as a Lean macro rule (as for the sweep in 1RB0LF_1LC0RB_0LD1LA_0RA1LE_0LA0RA_1LA---).
- Rounds grow about 2.2x in steps, so a round-level simulator could go far beyond 10^9.

## Reproduce

```sh
gcc -O2 -o tok holdouts/1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---/c/tok.c && ./tok 1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB--- 1000000000 C 1 R 0 1000000 0 | awk 'NR%400==1'
gcc -O2 -o nbhd holdouts/1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---/c/nbhd.c && ./nbhd 1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB--- 1000000000 E 0
python3 holdouts/1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---/py/rules.py > holdouts/1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---/lean/Rules.lean
```

## Pages

- [`pages/holdouts/1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---/explainer.html`](../../pages/holdouts/1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---/explainer.html)
- [`pages/holdouts/1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---/proof-status.html`](../../pages/holdouts/1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---/lean/check.sh
```
