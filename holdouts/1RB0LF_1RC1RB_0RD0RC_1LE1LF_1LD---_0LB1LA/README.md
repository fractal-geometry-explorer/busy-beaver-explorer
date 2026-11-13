# 1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA

bbchallenge id 116372. One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 1RC | 1RB |
| C | 0RD | 0RC |
| D | 1LE | 1LF |
| E | 1LD | --- |
| F | 0LB | 1LA |

## What it does

**Tape**: a short counter on the left, then `1^K 0^Z`. **Sample point**: C on a 0 at the right end (once a sweep).
At step 16,085,367: `11 0^6 111 0^8 1^21 0^7 1^2670 0^1377`.

**One sweep** (all passes are Lean shift rules in `lean/Rules.lean`): leftward, D/E turn the zeros into ones
(`d_run`), A/F turn the ones into `(10)^n` (`a_run`); near the counter the head turns and a zigzag turns `(10)^n`
back into ones, 10 steps a pair (`d_zigzag`); B crosses ones (`b_run`) and C turns the former zeros back into zeros
(`c_run`). 18,762 steps later: `... 1^21 0^6 1^2669 0^1381` (K -1 or -3, Z +4, the counter ticks).

**Phases (observed)**: when K is used up, the zeros become the new block. Phase starts near steps 5.8·10^5,
2.3·10^6, 9.4·10^6, 3.8·10^7, 1.5·10^8, 6.0·10^8 with tape lengths 838, 1678, 3358, 6718, 13446, 26894 (about
doubling, time x4).

**Halting**: E on a 1 is the only halt; E comes only from D on a 0, and D has a 1 on its left only when it came from E
on a 0. So it halts iff `1 D> 0` occurs (`halt_shape`). In 10^9 steps D read a 0 66,714,267 times, always with a 0 to
its left.

## Status

Open.

- **Lean, kernel** (`lean/Rules.lean`, from `py/rules.py`): `d_run`, `a_run`, `d_zigzag`, `b_run`, `c_run`,
  `halt_shape`, `halt_after_shape`. `lean/Blank.lean`: no halt in 10^7 steps.
- **Trusted**: no halt in 10^9 steps; near-miss counts (`c/nbhd.c`).
- **Heuristic**: the sweep/phase pattern (`c/tok.c`).

## Notes for later

- Chain the shift rules into a one-sweep macro rule `counter, 1^K 0^Z -> counter', 1^(K-d) 0^(Z+4)` (d = 1 or 3) and
  find the counter's rule (which d, when). Then the phase change, and a phase-level simulator past 10^9.

## Reproduce

```sh
gcc -O2 -o tok holdouts/1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/c/tok.c && ./tok 1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA 1000000000 C 0 R 0 10000000 0 | awk 'NR%2000==1'
gcc -O2 -o nbhd holdouts/1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/c/nbhd.c && ./nbhd 1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA 1000000000 D 0
python3 holdouts/1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/py/rules.py > holdouts/1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/lean/Rules.lean
```

## Pages

- [`pages/holdouts/1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/explainer.html`](../../pages/holdouts/1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/explainer.html)
- [`pages/holdouts/1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/proof-status.html`](../../pages/holdouts/1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA/lean/check.sh
```
