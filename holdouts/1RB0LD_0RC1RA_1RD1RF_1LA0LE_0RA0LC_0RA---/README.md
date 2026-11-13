# 1RB0LD_0RC1RA_1RD1RF_1LA0LE_0RA0LC_0RA---

bbchallenge id 149064. One of the six-state holdouts whose halting from blank tape is open (group G05, growth class
fixed/sqrt).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LD |
| B | 0RC | 1RA |
| C | 1RD | 1RF |
| D | 1LA | 0LE |
| E | 0RA | 0LC |
| F | 0RA | --- |

## Status

**Open.** A bouncer: the head sweeps between a counter at the left end and the right end of the tape, turning
the 8-cell word P into Q and back. The sweeps are proved; the counter, which decides where each sweep turns
back, is described only from observation.

- Lean, kernel (`lean/Blank.lean`): the halting configurations (`step_none_iff`), no halt in 10,000 steps.
- Lean, `native_decide` (`lean/Blank.lean`): no halt in 10,000,000 steps.
- Lean, kernel (`lean/Sweep.lean`, namespace `H149064`): `sweep_right`, `sweep_left` (via `cross_l2`, a shift rule
  with words carried on both sides of the head), `p_rotate`, the turns at the right end `turn_a`, `turn_b`, and the
  right halves of a round trip `round_a` (38n + 169 steps) and `round_b` (38n + 139 steps), for every n.
- Trusted (C, `c/snap.c` on `tools/c/tm.h`): no halt in the first 10¹¹ steps (505,176 cells visited).
- Heuristic: the counter structure below.
- Open: the rule of the counter, and halting.

## The sweeps

P = `11111010`, Q = `01010010`, W = `11110101` (P^n 1 = 1 W^n, `p_rotate`).

- Right: `A> Q^n` → `P^n A>` in 8n steps.
- Left: `W^n 1010 C> 101` → `1010 C> 101 Q^n` in 30n steps.
- Turn: `A> Q^(n+4) 0101 0^∞` → `P^(n+4) 1 1010 C> 101 0^∞` in 8n + 49 steps (`turn_a`), and
  `A> Q^(n+4) 0^∞` → `P^(n+3) 1 1010 C> 101 0101 0^∞` (`turn_b`). With the left sweep these give `round_a`,
  `round_b`: the head arrives at the left end of the run in state C with all of it turned into Q.

## The counter (observed)

Left of the long run the tape is a row of groups `11 P^a s P^b s' P^c`, with separators s, s' from `111010`,
`101111`, `101011`, `111111`; group lengths grow roughly geometrically to the right. Right of the run lie runs of Q.
At consecutive right-end turns near 3·10⁷ steps:

    30,354,281  … 11 P19 111010 P17 101011 P99 11 P4 101011 P4 101011 P26 101 Q234 010101 Q542
    30,360,081  … 11 P19 101111 P17 111111 P99 11 P4 111111 P4 111111 P27 101 Q233 010101 Q542
    30,373,293  … 11 P19 101011 P18 111010 P98 11 P5 101011 P5 101011 P32 101 Q226 010101 Q542
    30,378,699  … 11 P19 101011 P18 101111 P98 11 P5 111111 P5 111111 P33 101 Q225 010101 Q542
    30,392,939  … 11 P19 101011 P18 101011 P98 11 P6 101011 P6 101011 P38 101 Q218 010101 Q542

The last group alternates `101011/101011` and `111111/111111` and grows by 8 words per two trips, eating the
nearest Q run at the same rate; the group before it cycles its second separator through `101011`, `111111`,
`111010`, `101111`, one step per trip, shifting a word between its runs; earlier groups change more rarely. When
the Q run is used up a new group `11 P2 101011 P2 101011 P14` is built and the next Q run is eaten. So each
leftward sweep passes through the last few groups, changes each a little, and turns at the first group that does
not pass the change on, like the carry of a counter.

## Halting

The machine halts only when state F reads a 1. The proved sweeps and turns never do, so a halt can only come from
the work at the left turn.

## Reproduce

```sh
python3 holdouts/1RB0LD_0RC1RA_1RD1RF_1LA0LE_0RA0LC_0RA---/py/gen_sweep.py > holdouts/1RB0LD_0RC1RA_1RD1RF_1LA0LE_0RA0LC_0RA---/lean/Sweep.lean
gcc -O2 -o snap holdouts/1RB0LD_0RC1RA_1RD1RF_1LA0LE_0RA0LC_0RA---/c/snap.c && ./snap 1RB0LD_0RC1RA_1RD1RF_1LA0LE_0RA0LC_0RA--- 100000 30354281   # tape at a step
gcc -O2 -o sweeps holdouts/1RB0LD_0RC1RA_1RD1RF_1LA0LE_0RA0LC_0RA---/c/sweeps.c && ./sweeps 1RB0LD_0RC1RA_1RD1RF_1LA0LE_0RA0LC_0RA--- 30000000 31000000 1000   # turning points
```

## Pages

- [`pages/holdouts/1RB0LD_0RC1RA_1RD1RF_1LA0LE_0RA0LC_0RA---/explainer.html`](../../pages/holdouts/1RB0LD_0RC1RA_1RD1RF_1LA0LE_0RA0LC_0RA---/explainer.html)
- [`pages/holdouts/1RB0LD_0RC1RA_1RD1RF_1LA0LE_0RA0LC_0RA---/proof-status.html`](../../pages/holdouts/1RB0LD_0RC1RA_1RD1RF_1LA0LE_0RA0LC_0RA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LD_0RC1RA_1RD1RF_1LA0LE_0RA0LC_0RA---/lean/check.sh
```

## For later

- The exact rule of the left turn: what a leftward sweep does to each group it passes and where it stops, as a
  function of (a, s, b, s', c). Prove those passes in Lean as with `round_a` (symbolic runs plus `cross_l2`).
- With that rule, an accelerated simulator over groups (the segment simulator of
  `holdouts/1RB0LD_0RC---_0RD0RF_1LE0LA_1LF1LE_1RA0RD/py/segsim.py` runs this machine but finds no cycles to jump,
  about 7·10⁸ steps in 40 s).
- The Q runs at the right (`Q^269 010101 Q^542`): how they are made, and whether they form a second counter.
