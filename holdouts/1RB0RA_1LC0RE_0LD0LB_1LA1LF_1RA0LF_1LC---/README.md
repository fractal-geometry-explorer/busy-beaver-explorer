# 1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---

bbchallenge id 32883. Open. An exact **ternary counter**, least significant digit at the left end, whose digits are
pairs of long runs of alternating cells; each trip of the head from the left end and back adds one. The increment is
proved in Lean for every carry depth (kernel). What is not proved: what happens when a run that the counter keeps
shrinking runs out (a *transfer*, which moves a long run to the right end), and the right end itself.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RA |
| B | 1LC | 0RE |
| C | 0LD | 0LB |
| D | 1LA | 1LF |
| E | 1RA | 0LF |
| F | 1LC | --- |

## The tape as runs

Cut the tape into maximal runs of alternating cells (`0101...` or `1010...`): two neighbouring runs meet at a
doubled cell, `00` or `11`. So the tape is a list of run lengths, and the cells follow from the lengths (the first run
starts with 0). At the start of a trip (A at the left end of the visited tape) name the runs

    r0 r1 | x1 y1 | x2 y2 | x3 y3 | ...

Digit 0 is (r0, r1), digit k is (x_k, y_k). Its value is read from the lengths **mod 4**:

| value | digit 0 (r0, r1) | digit k (x_k, y_k) |
|---|---|---|
| 0 | (0, 3) | (2, 3), or (3, 3) while a decrement is pending |
| 1 | (2, 2) | (0, 2), or (1, 2) pending |
| 2 | (3, 1) | (1, 1), or (2, 1) pending |

("Pending": after digit k changes, x_k is one cell longer than the reading until digit k-1 next goes from 0 to 1,
which takes that cell; see the last row of the next table.) For example at step 10,000,025,550 (trip 30,932) the runs
are `82476 16507 | 82426 3897 | 36473 2653 | 33442 423 | ...`: digits 0, 2 (pending), 2, 0. Three trips later
(step 10,000,951,218) digit 0 has gone 0, 1, 2 and carried; the carry passed digits 1 and 2 and stopped at digit 3:
`82484 16511 | 82423 3899 | 36471 2655 | 33441 426 | 74 75 | ...`.

## One trip

Going right, A flips every cell it passes (`a_right`, `01 01` -> `10 10`); going left, B and C carry the pattern
one cell along (`b_left`, `c_left`). Every trip adds one to the counter:

| digit | change | runs |
|---|---|---|
| 0 | 0 -> 1 | r0 + 2, r1 + 3, x1 - 1 |
| 0 | 1 -> 2 | r0 + 5, r1 - 1 |
| 0 | 2 -> 0, carry | r0 + 1, r1 + 2 |
| k | 2 -> 0, carry | x_k - 2, y_k + 2 |
| k | 1 -> 2 | x_k + 2, y_k - 1 |
| k | 0 -> 1 | x_k - 1, y_k + 3, x_(k+1) - 1 (this is the pending decrement) |

A carry is a bounce: B meets the `00` at the start of x_k, goes back over y_(k-1) to the end of x_(k-1), turns
(B on a 1) and runs on through digit k. Where the carry stops the head turns and goes home; the left end grows by 4
cells per trip. The run lengths change by small steps, so the digit values stay readable; over one cycle of digit k
(3^(k+1) trips) x_k loses 4 cells and y_k gains 4; r0 gains 8 and r1 gains 4 every 3 trips.

## What is proved (Lean, kernel only, `lean/Counter.lean`)

The pieces of a trip, each for all lengths and every tape around it (`py/counter.py` writes them from
`tools/py/bbtools/symtm.py`):

| theorem | what | steps |
|---|---|---|
| `inc0` | digit 0 from 0 to 1: `0^inf A> (0101)^a+1 (1010)^b+1 101 10 R` | 8a+8b+26 |
| `inc1` | digit 0 from 1 to 2: `0^inf A> (0101)^a+1 01 (1010)^b+1 10 R` | 8a+16 |
| `out0` | digit 0 at 2, the carry leaves it | 4a+4b+12 |
| `carry` | the carry passes a digit at 2, `(0101)^c+2 0 (0101)^d+1 0` (e: the previous digit's d) | 4c+4d+8e+26 |
| `absorb1` | the carry stops at a digit at 1, `(0101)^c+1 (1010)^d+1 10` | 8c+12e+26 |
| `absorb0` | the carry stops at a digit at 0, `(0101)^c+1 01 (1010)^d+1 101`, next digit `10...` | 8c+8d+12e+44 |
| `home` | going home over a passed digit | 4c+4e+14 |
| `home0` | going home over digit 0; the left end grows by 4 | 4a+10 |

and chained by induction over the list of digits the carry passes: `carry_chain`, `home_chain`, and the whole trip
for **every carry depth** at once, `trip_stop1` (the carry stops at a digit at 1) and `trip_stop0` (at a digit at 0).
With `inc0` and `inc1` that is every kind of trip in the regular regime, with the exact tape after it and the exact
step count. The run-length table above is read off these statements (checked for random parameters by direct
expansion).

The minimum lengths these theorems need: r0 >= 7 and r1 >= 5 (or as in `inc0`, `inc1`), x_k >= 9 and y_k >= 5 for a
digit the carry passes, x >= 4, y >= 6 (stop at 1) or x >= 6, y >= 7 and the next digit starting `1 0` (stop at 0).

## How much of the run that covers

`py/rsim.py` is the machine on a run-length tape with the three proved sweep moves; it agrees with a plain cell
simulator on the step of all 17,669 trip starts in the first 4·10^9 steps. Classifying every trip start in the first
3·10^12 steps (726,270 trips): 725,254 (99.86%) are one of the four proved kinds (242,079 `inc0`, 242,079 `inc1`,
120,552 stop at 0, 120,544 stop at 1; `py/classify.py`). The other 1,016: the carry reaches the right end (98), a
run is too short for the theorems (269), or a digit has residues outside the table (648), and one is the first trip. They come, as far as we
have looked, with two irregular events (observed only):

* **Transfers.** x_k shrinks by 4 per cycle of its digit, so it runs out (to 2 or 1 cells). The next carry that
  reaches it does not bounce through: the head shuttles between the right end of y_(k-1) and the right end of the
  tape, taking two cells off y_(k-1) and adding two at the far right on every shuttle. y_(k-1), a long run, is moved
  to the right end, the digits past it are re-paired, and the counter goes on with fewer digits. Example, step
  39,282: `187 97 2 31 25 7 7` becomes `186 43 27 5 13 177`. These are the long gaps between trips (no trip starts between steps 8.6·10^11 and
  10^12, for instance) and the reason the right side of the tape grows.
* **The right end**, where new digits are made from short runs (`... 7`, `... 7 7`, `11 5`, `14 4`, `19 31`, ...).

## Halting

The only halting transition is F on a 1. F comes from E on a 1 (after B wrote a 0 just left of it, so F reads that 0)
or from D on a 1, and D only from C on a 0. So the machine halts exactly if D reads a 1 whose left neighbour is a 1:
C, moving left, meets `1 1 0`. Call k the length of the alternating stretch that ends at D's cell; a halt needs
k = 1. In the first 3·10^12 steps D read a 1 6,032,756 times: k = 2 158 times, k = 3 17 times, never k = 1; the
small cases we looked at came near the right end or in transfers. The regular trips cannot halt: the theorems above give their whole run.

## Status

Open. Kernel: halting configurations, 10,000 steps, the sweep moves (`lean/Rules.lean`), the counter's increment
for every carry depth (`lean/Counter.lean`). Native: 10^7 steps. Trusted: no halt in the first 10^14 steps (3,153,668 trips, 23,850,932 cells,
6 minutes, `py/rsim.py`). Heuristic: the counter reading, the transfers, the right end.

## For later

* State a transfer as a rule (a shuttle lemma with the run y_(k-1) and the digits it passes as parameters) and the
  re-pairing it leaves; then the right end. With both, the counter would close up into a proof (or show a halt).
* A closed tape language with run lengths kept mod 4 is a natural target; a first try (n-grams of run classes)
  grew without bound.

## First look

Growth class **sqrt/sqrt** (left: sqrt, exponent 0.554; right: sqrt,
exponent 0.389). After 1,000,000,000 steps: 76,685 cells visited (39,628 left of the
start, 15,538 right), 38,338 ones.

- left, step 976,307,423: `B>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- left, step 991,943,199: `B>0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- right, step 929,547,037: `1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `
- right, step 976,138,013: `1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 `

## Pages

- [`pages/holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/explainer.html`](../../pages/holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/explainer.html)
- [`pages/holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/proof-status.html`](../../pages/holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/lean/check.sh
python3 holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/counter.py > /tmp/Counter.lean   # regenerates lean/Counter.lean
python3 holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/rsim.py 1e12 100000
python3 holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/classify.py 3e12   # about a minute
gcc -O2 -o ev holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/c/ev.c && ./ev 1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC--- 2000000000 L B 1 100000 12 | awk 'NR%100==0'
```
