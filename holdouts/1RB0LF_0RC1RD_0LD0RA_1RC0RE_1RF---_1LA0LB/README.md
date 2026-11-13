# 1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB

bbchallenge id 79385. A six-state holdout of group G05 (growth class fixed/sqrt). **Open.** The tape is a sea
of `1010` holding *trains*, stretches of a second sea `1110 1110 ...`; the head eats the nearest train one word per
sweep, and a rare trip to the far left end turns every stretch of sea back into a full train, like a counter that
counts down and is reloaded. Lean proves a halt needs the word `A>0 1 1 1`: A stepping into the front of a train.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 0RC | 1RD |
| C | 0LD | 0RA |
| D | 1RC | 0RE |
| E | 1RF | --- |
| F | 1LA | 0LB |

## What it does

**Two seas.** Most of the tape is the sea `1010...`; the rest is *trains*, stretches of the second sea `1110 1110
...`, separated by short markers. The left end is fixed (cell −14); the right end grows by 2 cells per sweep. The
head lives at the right end and sweeps left, as far as the nearest train, and back.

**One sweep eats one word** (`sweep_train`, kernel, for all a, b and every tape L left of the train):

    L 1110 (10)^(b+1) 110 110 (10)^(a+1) 11 C> 0^inf
      --(8a + 8b + 76 steps)-->
    L 1010 (10)^(b+1) 110 110 (10)^(a+2) 11 C> 0^inf          i.e.  L (10)^(b+3) 110 110 (10)^(a+2) 11 C>

The last word `1110` of the train becomes `1010` (one cell flips), so the train loses one word and the sea in front
of it gains two; the right end gains two cells. So the time between two right-end records grows by 24 steps per
sweep while one train is being eaten (the tape grows by 2 cells and each cell costs about 12 steps per round trip).

**A counter that counts down and is reloaded.** The trains sit at fixed distances from the left end. Sampled at the
right-end records (`py/trains.py`), the head eats the nearest train word by word; when it is gone the head goes on
to the next one, and so on. New trains appear in bursts: a trip that goes further than the nearest train turns the
sea it crosses into trains. At step 2,510,806, after the last train (5 words, at the left end) had been eaten, one
trip to the left end reloaded the whole tape: trains of 397, 37, 69, 9, 13, 12, 15, 13, 7, 2, 2, 2, 2, 3 and 5
words, each stretch of sea filled to the next marker, most of them one or two words longer than before. Then the
eating starts again. The trips that come near the left end are the rare carries (`c/deepR.c`, the leftmost cell
reached per doubling of the step count): the reload at step 2,510,806 went to cell 126; up to 1.3·10^8 steps
trips came within 1,000 cells of the left end in every doubling (down to cell 486), after that only twice: cell 378
(between 5.4·10^8 and 1.1·10^9 steps) and cell 936 (between 1.7·10^10 and 3.4·10^10); in the other doublings up to
6.9·10^10 the head stayed right of cell 6,600.

**Where it could halt.** It halts on `E1`. E is entered only from `D1`, D only from `B1`, and B from `A0` or from
`F1` (which writes the 0 that D would then read). So **three steps before a halt the head is A on a 0 followed by
`1 1 1`** (`halt_needs_A0111`, kernel): A, moving right, steps onto the 0 just in front of a train word `111`. In
the run A meets `0 1 1 0` (the same with an ordinary junction) about 8,500 times in 3·10^8 steps, at the markers
and the trains' edges, but never `0 1 1 1` (`c/a011.c`). Whether a reload or a carry can ever bring A to the front
of a train in that phase is the open question.

## Status and evidence

**Lean, kernel** (`lean/Halt.lean`): `halt_needs_A0111`. **Lean, kernel** (`lean/Rules.lean`, written by
`py/gen_rules.py` with `bbtools.symtm.prove`): `sweep_train`. **Lean** (`lean/Blank.lean`, generated):
`step_none_iff`, no halt in 10^4 steps (kernel), 10^7 (`native_decide`).

**Computed (trusted)**: no halt in the first 10^11 steps (`c/deepR.c`, direct simulation, which also gives the
leftmost cell reached per doubling of the step count); `c/a011.c` counts the near misses `A>0 1 1`.

**Heuristic**: the counter picture (`py/trains.py`): read off samples, not proved.

**Open**: whether A ever steps onto the front of a train.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB/lean/check.sh
cd holdouts/1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB
python3 py/gen_rules.py > /tmp/Rules.lean                                        # regenerates lean/Rules.lean
gcc -O2 -o snapR c/snapR.c && ./snapR 1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB 3000000 1 C > s.txt && python3 py/trains.py s.txt
gcc -O2 -o deepR c/deepR.c && ./deepR 1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB 1000000000
gcc -O2 -o a011 c/a011.c && ./a011 1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB 300000000
```

## First look

Growth class **fixed/sqrt** (left: fixed, exponent 0.0; right: sqrt,
exponent 0.514). After 1,000,000,000 steps: 47,842 cells visited (14 left of the
start, 35,601 right), 29,338 ones.

- right, step 970,239,288: `1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1 0^2 1^3 0 1^3 0 1^3 0 1^2 0 1^2 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1^2 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1^4 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1^4 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1^4 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1 0^2 1^3 `
- right, step 985,942,446: `1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1 0^2 1^3 0 1^3 0 1^3 0 1^2 0 1^2 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1^2 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1^4 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1^4 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1^4 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1^2 0 1 0^2 1^3 `

## Pages

- [`pages/holdouts/1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB/explainer.html`](../../pages/holdouts/1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB/explainer.html)
- [`pages/holdouts/1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB/proof-status.html`](../../pages/holdouts/1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB/lean/check.sh
```

## For later

An exact macro machine: the list of markers and trains with the seas between them, the rule for a sweep that finds
the nearest train empty (where it turns, what it changes), and the reload rule (which stretch becomes how long a
train). With that the halting question becomes a question about the counter, as for the machines finished in this
group.
