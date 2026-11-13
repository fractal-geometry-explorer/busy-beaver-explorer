# 1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF

bbchallenge id 58953. One of the six-state holdouts whose halting from blank tape is open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 1RC | 1RB |
| C | 1RD | 0RA |
| D | 0RE | --- |
| E | 1LF | 1LA |
| F | 1LA | 1LF |

## What it does

**Sample point**: the head in A at the left end. The tape is then a list of blocks `1^k 0` with k odd and **every 0
single**: k = 1 mod 4 in the left part, k = 1 or 3 mod 4 further right. Example at step 100,542 (each block as its k):

    9 1 5 1 1 1 9 1 5 1 9 1 5 1 1 1 21 1 1 1 5 1 5 1 1 1 1 1 1 1 17 1 1 1 5 1 1 1 1 1 1 1 5 7 1 3 1 5 1 5 1 5 15 ...

**Sweeps**: a bouncer. Leftward, F runs over 1s; at a 0 it fills it and A/E turn each `11` into `01` until the next 0.
Rightward, B runs over 1s and A/B/C turn `0101` into `1110`. Each sweep rewrites the blocks from their neighbours,
like one step of a cellular automaton: the space-time diagram is full of nested (Sierpinski-like) triangles. Most
sweeps turn back inside the left part; the right part stays frozen until a rare deep sweep reaches the right end (steps
1.9·10^6, 6.4·10^6, 1.9·10^7, 6.1·10^7, 1.9·10^8, 5.8·10^8: about 3.1 times apart, the logarithmic side). The depth of
the sweeps behaves like the carries of a counter. No exact macro rule is known: the block values look chaotic.

**Halting**: D on a 1 is the only halt; D comes only from C on a 0, C only from B on a 0. So it halts iff B meets
`0 0 1`: a double zero inside the tape. In 10^9 steps B read a 0 followed by another 0 only 42 times, all at the blank
right end; the closest call was `B> 0 1 0 0` (6 times).

## Status

Open.

- **Lean, kernel** (`lean/Rules.lean`, from `py/rules.py`): `b_run`, `f_run`, `e_run`, `a_run` (the sweep rules),
  `halt_shape` (`B> 0 0 1` reaches D on a 1 in 2 steps), `halt_after_shape`. `lean/Blank.lean`: no halt in 10^7 steps.
- **Trusted**: no halt in 10^9 steps (triage); the double-zero count (`c/nbhd.c`). Twin: the right-end tapes are identical to those of
  1RB0LF_1RC1RB_1RD0RA_1RE0RE_1LF---_0LD1LA, which takes 1.5 times as many steps (`c/tok.c`, observed).
- **Heuristic**: the sweep picture, frozen right part, deep sweeps 3.1 times apart (`c/samples.c`).
- **Computed, negative**: `bbtools.ctl` K = 2..6 closes but allows halts (its right automaton doubles with K); n-gram
  CPS widths 3..7 fail.

## Notes for later

- The natural conjecture is "every 0 inside the tape stays single". It would prove non-halting. It is not a regular
  invariant at window size 6; it may need the block values mod 4 (left part 1 mod 4) and the counter-like depth.
- Find the exact one-sweep map on the list of block values (a CA rule on k mod 4?).

## Reproduce

```sh
gcc -O2 -o samples holdouts/1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/c/samples.c && ./samples 1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF 200000 A L 100000 3
gcc -O2 -o nbhd holdouts/1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/c/nbhd.c && ./nbhd 1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF 1000000000 B 0
python3 holdouts/1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/py/rules.py > holdouts/1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/lean/Rules.lean
```

## Pages

- [`pages/holdouts/1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/explainer.html`](../../pages/holdouts/1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/explainer.html)
- [`pages/holdouts/1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/proof-status.html`](../../pages/holdouts/1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_1RC1RB_1RD0RA_0RE---_1LF1LA_1LA1LF/lean/check.sh
```
