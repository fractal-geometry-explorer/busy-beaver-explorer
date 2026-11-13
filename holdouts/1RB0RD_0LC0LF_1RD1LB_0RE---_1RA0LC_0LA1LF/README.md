# 1RB0RD_0LC0LF_1RD1LB_0RE---_1RA0LC_0LA1LF

bbchallenge id 106698. One of the six-state holdouts whose halting from blank tape is open; analyzed by hand (group G02). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RD |
| B | 0LC | 0LF |
| C | 1RD | 1LB |
| D | 0RE | --- |
| E | 1RA | 0LC |
| F | 0LA | 1LF |

## What it does

The head sweeps between the ends over a background of `100` blocks carrying a few short defects. Writing `a^k` for
`(100)^k`, at the steps where E reaches a new cell on the right:

    step 1,237,212:   10 a52 0 a22 10101010 a283 0 a358 1010 a102 0
    step 1,312,414:   10 a52 0 a21 11101010 a278 1 a344 1010 a162 0
    step 59,431,697:  10 a15 101010101010 a108 10101010 a1199 1110 a1 0 a954 1110 a747 1010 a3157 0

Each right sweep shifts the background by one cell (A: `100` to `001`, D: `001` to `010`); the defects alternate
between forms such as `1010` and `1110`, drift left at different speeds, and new ones are born at the right end.
Width 18,579 at step 59,431,697, about quadratic time.

## Status

Open. The only halt is D reading a 1; D is entered only from A1 = 0RD and C0 = 1RD.

- Lean, kernel: A on `1 1` and C on `0 1` halt (`halts_A_11`, `halts_C_01`); five shift rules over the background
  and the `1010` defects (`lean/Rules.lean`); halting configurations, 10^4 steps (`lean/Blank.lean`).
  `native_decide`: 10^7 steps.
- Computed: no halt in 10^10 steps (`tools/c/tmrun.c`, 69,643 ones); `bbtools.ctl` K = 2..7 allows a halt.

## Notes for later

- Catalogue the defects (their forms, speeds and phases), then what happens when two meet or one reaches the left
  end; a proof would show no meeting puts A on `11` or C on `01`.

## Pages

- [`pages/holdouts/1RB0RD_0LC0LF_1RD1LB_0RE---_1RA0LC_0LA1LF/explainer.html`](../../pages/holdouts/1RB0RD_0LC0LF_1RD1LB_0RE---_1RA0LC_0LA1LF/explainer.html)
- [`pages/holdouts/1RB0RD_0LC0LF_1RD1LB_0RE---_1RA0LC_0LA1LF/proof-status.html`](../../pages/holdouts/1RB0RD_0LC0LF_1RD1LB_0RE---_1RA0LC_0LA1LF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RD_0LC0LF_1RD1LB_0RE---_1RA0LC_0LA1LF/lean/check.sh
```
