# 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD

bbchallenge id 136824. One of the six-state holdouts whose halting from blank tape is open (group G07).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RC |
| B | 1LC | 0RE |
| C | 1LD | 0LB |
| D | 1RA | 1LC |
| E | 1RA | 1RF |
| F | --- | 1RD |

## What it does

Same first four states as 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC and the same frame (that README has the shared
description). A *visit* is a step at which the head extends the tape to the left in state D; the tape is then

    0^inf  D>0  1^n  R  0^inf ,   n even

and one sweep later it is the same with `n + 2` and a new `R` that does not depend on `n`, unless the head comes home
in state C (an **event**: the block becomes a fresh reservoir, `n` restarts at 2) or the machine halts.

Unlike its two siblings, this machine's counter is an honest one, and it was decoded. In pairs `a` = 01, `b` = 11,
the region at an even visit is

    a a a   S[s_0] S[s_1] ... S[s_(m-1)]   junk        S = [ baabaa, abbabb, bbbbbb, aaaaaa ]

* a **chain of counters mod 4**, 12 cells each. A double visit adds 1 to `s_0`; if `s_0` was 0 the sweep turns
  there, otherwise it goes on and does the same to `s_1`, and so on. So counter `j+1` is reached by 3 of every 4
  sweeps that reach counter `j`, and a sweep passes the whole chain once in about `(4/3)^m` double visits;
* a fresh reservoir `a^N` is this chain with all counters in state 3 (`aaaaaa`): the reservoir *is* the counter;
* the **junk** is what the previous epoch left (its last region, reworked by the event). It changes only at the
  sweeps that pass the whole chain, by a map that depends on the junk alone (3,000 recorded passes of epoch 3
  replayed behind four different chains: same result), and it behaves like the chaotic counters of the siblings: the passes go deeper and deeper into it.

The double visits that turn inside the chain are jumped by a closed formula, steps included (`py/chain.py`: `jump`,
`jump_steps`; a double visit from block `n` costs `6n + 146` steps, plus 128 for each counter passed in state 1 or
3 and 108 for each passed in state 2); only the passes are simulated cell by cell. This gives an exact accelerated
simulator (`c/chainrun.c`, 128-bit visit numbers, 256-bit step counts).

### The run so far

| epoch | starts at visit | region `R` | ends |
|---|---|---|---|
| - | 2 | a few cells | events after visits 3, 13, 23 |
| 1 | 24 | 65 cells | event after visit 97 |
| 2 | 98 | 217 cells: `aaa`, 12 counters, 67 cells of junk | event after visit 1,481 |
| 3 | 1,482 | 2,987 cells: `aaa`, 230 counters, 221 cells of junk | event after 25,741,416 passes of the chain |
| 4 | 2,802,669,472,598,490,952,316,788,103,359,480,650 | 2,802,669,472,598,490,952,316,788,103,359,479,170 pairs `a`, then 2,985 cells of junk | not before about (4/3)^(4.67e35) visits |

The third event:

| | |
|---|---|
| end of the last complete pass (visit) | 2,802,669,362,130,569,848,949,782,677,328,552,882 |
| first visit of epoch 4 (block `1^2`) | 2,802,669,472,598,490,952,316,788,103,359,480,650 |
| step of that visit | 23,564,868,517,906,510,281,033,392,402,285,525,944,194,469,908,788,408,626,361,071,990,157,929,983 |
| new region | `a^2,802,669,472,598,490,952,316,788,103,359,479,170` followed by a 2,985-cell tail ending `...babaaabaabaa 1` |

So the machine does not halt in its first 2.356e73 steps. Epoch 4 has a chain of 4.67e35 counters in front of
2,985 cells of junk. The first sweep that even reaches the junk comes after about (4/3)^(4.67e35) double visits,
i.e. about 10^(5.8e34) visits; and the junk of epoch 3 (221 cells) needed 25,741,416 such passes before it gave way.

### Where it can halt (proved)

The halting transition F0 is reached as `A>0 1 1 0` (A0 -> 1RB, B1 -> 0RE, E1 -> 1RF). `lean/Edge.lean` proves:

    theorem halt_at_edge : steps n init = some c -> step c = none -> c.st = .F /\ c.r = blank
    theorem halts_iff_edge : HaltsFromBlank <-> exists n c, steps n init = some c /\ c.st = .F /\ c.r = blank

i.e. the machine can only halt with the head on blank tape beyond the far (right) end. The proof is a closed tape
language whose automata remember the six nearest cells on each side of the head *and the parity of the distance to
the next 0* (98 left states, 50 right states, 5,545 abstract configurations; found by `py/fctl.py`, a variant of
`bbtools.ctl`). Plain windows cannot do this: the alignment of the pairs inside a long run of 1s is lost.

So between events the machine provably cannot halt (the sweeps that turn inside the chain or the junk never see
the far end); everything is decided when a pass reaches the far end of the junk.

## Status

Open (cryptid-like, but with an exact description of everything except the junk).

- **Kernel:** `lean/Blank.lean` (halting configurations; no halt in 10^4 steps).
- **native_decide:** `lean/Blank.lean` (10^7 steps); `lean/Edge.lean`: every halt from blank tape is in state F with
  blank tape from the head on (`halt_at_edge`, `halts_iff_edge`). The closure check of the certificate is by
  `native_decide` (too large for `decide`).
- **Computed (trusted):** the visit-level description and its accelerator. `py/test_chain.py` compares `py/chain.py`
  with the direct run: every visit (step count, block, region) up to visit 6,000 cell by cell, through the events
  after visits 97 and 1,481, then the jumps against the same data. `c/chainrun.c` is the same algorithm in C; it
  agrees with `chain.py` on visit, block, region and step count after 300 passes of epoch 3 (visit 3.3e31, step
  3.2e63), and its visit numbers agree with an independent earlier program (without step counts) at passes 1 to 7
  million and at the event. Result: the third event as in the table, and no halt before it.
- **Heuristic:** in the small-block model (`smallblock`, block cut to 4 cells, random regions of 8 pairs) all of 2,000
  runs halt, within 12 events, each time at the blank far end, as the theorem says. With the last 21 or 41 cells of
  the true tail of epoch 4 at the far end of a random region, none of 400 runs halts at the first contact.
- **Open:** whether some event halts. The junk has no regular digits (blocks of 18, 28 and 28 cells at its start
  behave like digits with 55, 181 and more than 292 states, then the pattern is lost).

```sh
python3 holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD/py/test_chain.py 6000      # chain.py against the direct run
gcc -O2 -o chainrun holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD/c/chainrun.c
./chainrun -direct 1488 s1488.txt                  # the state of the direct run at visit 1488 (epoch 3)
./chainrun s1488.txt 1000000000 s_end.txt          # to the double visit of the third event (about 80 minutes);
                                                   # the result is kept in c/state_event3.txt
python3 holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD/py/chain.py s_end.txt 1   # replay it: the event, the new tail (c/event3.txt)
python3 holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD/py/fctl.py 1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD 6   # the tape language
```

## Next steps

A decision needs the law of the junk at the passes (an autonomous map on a few thousand cells): which of its
far-end contacts halt. For epoch 4 that is a question about the 2,985-cell tail recorded by `chain.py`; the number
of passes it needs is probably far beyond simulation (the 221 cells of epoch 3 took 2.6e7), but unlike for the
siblings each pass costs one map application, not an exponential number of sweeps.

## Pages

- [`pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD/explainer.html`](../../pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD/explainer.html)
- [`pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD/proof-status.html`](../../pages/holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD/lean/check.sh
```
