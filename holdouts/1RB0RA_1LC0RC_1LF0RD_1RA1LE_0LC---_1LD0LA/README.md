# 1RB0RA_1LC0RC_1LF0RD_1RA1LE_0LC---_1LD0LA

bbchallenge id 26127, group G10, family F08 (a counter beside a chaotic edge). Whether it halts from blank tape is
**open**. Family: **bouncer with a multi-digit counter of 011 blocks**, regular in its first three digits and
irregular beyond.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RA |
| B | 1LC | 0RC |
| C | 1LF | 0RD |
| D | 1RA | 1LE |
| E | 0LC | --- |
| F | 1LD | 0LA |

## What it does

The tape grows to the left, one sweep at a time; at the end of each sweep the head extends the tape on the left in
state D. Read from there, the tape is blocks `a = 011` repeated, separated by short separators (`1`, `01` or
`111`; a few other words occur only near the right end):

    a^n0 S1 a^n1 S2 a^n2 S3 a^n3 S4 a^n4 ...

At step 3·10^9 (sweep 21,693; `c/leftsnaps.c`, `py/levels.py`):

    a^21693 01 a^4 1 a^5433 1 a^4 01 a^21 1 a^5 111 a^1395 1 a^69 01 a^101 111 a^59 01 a^65 01 a^44 1 a^42 ...

Each sweep runs right from the left end over the first block, rewrites the separators it meets and turns back
somewhere, zigzagging back and forth across the small blocks on the way. It acts like an odometer whose digits are
the separators:

- **Level 1** (S1, n1, S2) is exactly periodic with period **8 sweeps** from sweep 10 on, and n0 grows by one per
  sweep. The configuration at the start of each of the eight sweeps of the cycle, and how far that sweep changes
  the tape (n0 odd or even):

  | row | S1 | n1 | S2 | n0 | the sweep starting here changes |
  |---|---|---|---|---|---|
  | 1 | 1 | 4 | 1 | odd | deep into the tape (a carry) |
  | 2 | 1 | 4 | 1 | even | S1 only: `1` becomes `01` (Lean `sweep_1`) |
  | 3 | 01 | 4 | 1 | odd | S1 and n1: `01` becomes `111`, n1 − 1 (Lean `sweep_01`) |
  | 4 | 111 | 3 | 1 | odd | up to level 2 |
  | 5 | 1 | 4 | 01 | odd | up to level 2 |
  | 6 | 1 | 5 | 111 | even | S1 only (Lean `sweep_1`) |
  | 7 | 01 | 5 | 111 | odd | S1 and n1 (Lean `sweep_01`) |
  | 8 | 111 | 4 | 111 | odd | deep into the tape (a carry) |

  The four sweeps marked Lean are proved for every length of the blocks and every tape beyond them.
- **Level 2** (S3, n3, S4) is exactly periodic with period **16 sweeps** from sweep 60 on; n2 grows like n0/4.
- **Level 3** (S5, n5, S6) is exactly periodic with period **64 sweeps** from sweep 224 on; n4 stays at 21.
- **Level 4 and beyond** have no period up to 4,096 sweeps in the first 3·10^9 steps; n6 grows like n0/16, the
  later blocks are of irregular sizes (tens to a hundred).

So the machine is a counter with exact low digits and a chaotic tail, a variant of the "counter beside a chaotic
edge" of family F08: the chaotic part is the high end of the counter, which the sweeps reach less and less often.

## Halting

The only halting transition is E on 1, and E is entered only from D on 1 (moving left). So a halt is `1 D> 1`: D
reading a 1 with a 1 on its left (Lean: `halt_D`). In the sweeps D meets a separator starting with 1 only right
after a block rewritten to `100`, so the cell on its left is a 0; a halt needs two separators side by side, or a
separator of an unusual shape. `bbtools.ctl` finds closed tape languages (windows of 2 to 6 cells) that cover the
run but still allow halts, with only a local constraint near the head: at K = 6 the head cell and the cells to its
right read `111101`.

## What is proved, and where

- `lean/Blank.lean` (generated): the halting configurations; no halt in 10^4 steps (kernel) and 10^7 (`native_decide`).
- `lean/Rules.lean` (kernel, written by `py/rules.py`): the rightward crossing `walk_DA` (D and A take turns over
  the blocks); the sweeps `sweep_1` and `sweep_01` for all block lengths and any tape beyond; the halting situation
  `halt_D`.
- Trusted computation: `tools/c/rleaccel.cpp` with blocks of 6 cells finds no halt in 3.1·10^16 steps (tape 2.8·10^8
  cells); `py/levels.py` on the sweeps of the first 3·10^9 steps gives the periods above.

## Deciders tried without success

`bbtools.ctl` with windows K = 2..6 (no closed language without halts), `ngramcps` with widths 2..6, plain and with
`-H 2`, `-H 3`, `-U`.

## For later

- The rules of all eight sweeps of level 1, then a "level" lemma: what one carry into level j does to the blocks
  of level j and what it sends on. The periods 8, 16, 64 suggest the low levels can be written as a closed rule.
- What happens past level 3: is the tail a counter of another kind, or does it carry in an irregular order?
- Same family as 1RB1LD_1LC---_1RE0LD_1LC1LD_1RF0RE_1RA0RC.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RA_1LC0RC_1LF0RD_1RA1LE_0LC---_1LD0LA/lean/check.sh
python3 holdouts/1RB0RA_1LC0RC_1LF0RD_1RA1LE_0LC---_1LD0LA/py/rules.py      # rewrites lean/Rules.lean
gcc -O3 -o /tmp/leftsnaps holdouts/1RB0RA_1LC0RC_1LF0RD_1RA1LE_0LC---_1LD0LA/c/leftsnaps.c
/tmp/leftsnaps 3000000000 | python3 holdouts/1RB0RA_1LC0RC_1LF0RD_1RA1LE_0LC---_1LD0LA/py/levels.py
g++ -O2 -o /tmp/rleaccel tools/c/rleaccel.cpp && /tmp/rleaccel 1RB0RA_1LC0RC_1LF0RD_1RA1LE_0LC---_1LD0LA 6 3000000000 ck.bin 300
```

## Pages

- [`pages/holdouts/1RB0RA_1LC0RC_1LF0RD_1RA1LE_0LC---_1LD0LA/explainer.html`](../../pages/holdouts/1RB0RA_1LC0RC_1LF0RD_1RA1LE_0LC---_1LD0LA/explainer.html)
- [`pages/holdouts/1RB0RA_1LC0RC_1LF0RD_1RA1LE_0LC---_1LD0LA/proof-status.html`](../../pages/holdouts/1RB0RA_1LC0RC_1LF0RD_1RA1LE_0LC---_1LD0LA/proof-status.html)
