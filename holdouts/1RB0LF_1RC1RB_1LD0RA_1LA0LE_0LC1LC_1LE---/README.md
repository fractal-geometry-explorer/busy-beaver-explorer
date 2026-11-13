# 1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---

bbchallenge id 12600. A BB(6) holdout, group G10 (one side of the tape grows like the square root of the step count, the other more slowly). Analysed by hand from the generated folder.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 1RC | 1RB |
| C | 1LD | 0RA |
| D | 1LA | 0LE |
| E | 0LC | 1LC |
| F | 1LE | --- |

## What it does

**One background, two forms.** After a sweep to the right the tape repeats `0111`; a sweep to the left turns
each `01110111` into `01001111`, and the next rightward sweep turns it back. The four shift rules of these sweeps
are proved (`lean/Rules.lean`).

**A few defects.** Two consecutive end turns:

```
step 394,721,780  right end  (1110)^3460 1^8 0 1^3 0 1^6 (0111)^200 1^17 (0111)^1206 110 1^3 0 1^7 0 1^3 0 1^6 (0111)^74 (1110)^3 1100
step 394,821,133  left end   0 (01001111)^1731 1^5 0100 1^7 (01001111)^100 1^17 (01001111)^603 110100 1^8 0100 1^7 (01001111)^36 ...
```

Four to six short defects (`1^8 0 1^3 0 1^6`, `1^17`, ...) separate long, uneven domains (3460, 200, 1206, 74 copies
here; 1676, 6498, 10, 552, 1018 at step 1.5·10^9). At the left end a block `1^N` grows by about one cell per sweep
while the domain next to it shrinks.

## Halting

F1 is the only halting transition, reached as `1 A>1`. It cannot happen inside a domain; whether a defect ever
produces it is open.

## What is proved

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10^4 steps (kernel) and 10^7 (`native_decide`).
- `lean/Rules.lean` (from `py/rules.py`, kernel): the four sweep rules over the background (`b_right`, `c_right`, `d_left`, `c_left`).
- Computed (`tools/c/triage.c`): no halt in 10^9 steps.

Everything else on this page is heuristic: read off runs of up to 2·10^9 steps (`tools/c/tokrun.c`), not proved.

## For later

- Write each defect type as a rule for a full sweep (in both directions), to see how far it moves and how it changes
  the domains next to it; with that the run could be accelerated far beyond 10^9 steps.

## Reproduce

```sh
python3 holdouts/1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---/py/rules.py | diff - holdouts/1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---/lean/Rules.lean   # the rules file is current
gcc -O2 -o tokrun tools/c/tokrun.c
./tokrun 1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE--- 400000000 x=0 LR 2000 | tail -4   # the tape each time the head extends it (x is a 0)
```

## Pages

- [`pages/holdouts/1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---/explainer.html`](../../pages/holdouts/1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---/explainer.html)
- [`pages/holdouts/1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---/proof-status.html`](../../pages/holdouts/1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LF_1RC1RB_1LD0RA_1LA0LE_0LC1LC_1LE---/lean/check.sh
```
