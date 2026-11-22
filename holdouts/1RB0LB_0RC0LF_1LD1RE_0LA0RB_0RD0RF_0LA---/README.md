# 1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---

bbchallenge id 112145. One of the six-state holdouts whose halting from blank tape is open (group G11).

Family **G11-Y** (two counters ticking together, `1RB0LB_0RC0LD` and relatives): this machine is a disguised copy (B1 = 0LF with F0 = 0LA, so F reading 0 acts as D; D1 = 0RB; E1 = 0RF): the same left-end extensions to within a few hundred steps, and E1 rare.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LB |
| B | 0RC | 0LF |
| C | 1LD | 1RE |
| D | 0LA | 0RB |
| E | 0RD | 0RF |
| F | 0LA | --- |

## What it does

The tape is, most of the time, `L · engine · R`. Every visit of the head to the engine (an *event*) adds 1 to two binary
counters, one on each side. In the reference machine `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---`, `L` is in 4-cell blocks (`0101` = 1,
`0001` = 0, lowest digit next to the engine) and `R` has one cell per digit, three cells apart (cells 9, 12, 15, … right
of the head), lowest digit nearest the engine. Between some digits of `R` there are fixed stretches (junk) that the carries cross.

- **Left side: clockwork.** When `L` overflows the carry reaches the left end, the tape grows by two cells and `L`
  restarts. The busiest cell (the lowest digit of `L`) turns exactly 2^k times between consecutive left-end extensions, each power twice: 64, 64, 128, 128, …, 2^24
  (first 1.5·10^9 steps, `ymax.c`).
- **The junk.** The change counts per cell (`chg.c`: how often each cell changes between consecutive events over a
  whole period) halve from one digit to the next, with junk stretches between some digits. The junk is written when a
  carry reaches the end of the tape (at irregular event counts); how is not decoded.
- **Where it can halt.** Only in F reading 1; F is entered from B1 (0LF) and E1 (0RF). After B1, used about 4·10^7 times in 10^9 steps, the head has read a 0 every time. E1 is the rare one: 306 uses in 10^9 steps, each followed by a 0, as in the reference machine, where in the reference machine E1 fires when a carry of the right counter reaches a digit for the first time since the last left-end visit: right after the visit at step 2,188,604 it fires at steps 2,188,675, 2,188,767, 2,188,882, 2,189,117, 2,189,592, 2,190,547, 2,192,462, three cells further right each time and after twice the wait each time, as a binary counter reaching new digits.

The family: `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---` (reference), `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---` (the same run, checked cell for cell for
10^10 steps), `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---`, `1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---`,
`1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---` (left-end extensions after 2^k events, each twice, within a few hundred
steps of each other), `1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---` and `1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---` (same
right part at the left-end visits, 3·2^k), and the mirror case `1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---`.

<!-- F02-visit-law:begin -->
## The visit law, and where the run leaves the PR59 machines (F02, 13 November 2026)

**Proved in Lean (kernel), `lean/Visit.lean`.** A *visit*: the head enters a stream `s` (all cells from some cell on)
in state C with a 0 on its left, and comes back in state A two cells further left, the 0 restored and `s` rewritten
to `v(s)`. `Vis s s'` says exactly that, for every tape to the left. The rules, for every stream `s`:

| stream | after the visit | theorem |
|---|---|---|
| `0 s` | `1 s` | `vis_0` |
| `100 s` | `000 v(s)` | `vis_100` |
| `110 s` | `000 v(s)` | `vis_110` |
| `1010 s` | `1010 v(v(s))` | `vis_1010` |
| `1011 s` | `0001 s` | `vis_1011` |
| `111 s` | the machine halts | `vis_111_halts` |

`111 s` halts the machine (`vis_111_halts`). The six prefixes 0, 100, 110, 111, 1010, 1011 cover every stream, so the
rules are the whole machine: it halts from blank tape only if some visit meets `111` (each rule is a theorem; this
"only if" is read off the case list and is not itself stated in Lean).

The run is a sequence of rounds (`start`, `round`, `round_halts`): after 4 steps the tape is `0^inf A> 1 0 S_1` with
`S_1 = 1 0^inf`, and a round turns `0^inf A> 1 0 S` into `0^inf A> 1 0 S'` with `S' = v(1 0 S)`. If a nested visit
halts, so does the visit around it (`vis_100_halts_1`, `vis_110_halts_1`, `vis_1010_halts_1`, `vis_1010_halts_2`).

**The same first four rules as the machines of busycoq PR59.** `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---` and its two
relatives obey `0 s -> 1 s`, `100 s -> 000 v(s)`, `110 s -> 000 v(s)`, `1010 s -> 1010 v(v(s))` too, with the same
rounds; they halt on `1011` (on `111` the three differ). PR59 proves in Rocq that they halt: rounds 1 to 161,210 use
only those four rules and round 161,211 meets `1011`. This machine differs only in what it does on `1011` and `111`.

**Computed (not proved): this machine does not halt there.** `c/vis.c` in
`../1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---/` runs the visit law with counts (2^j visits cross the word
in round 2j; counts are kept as 2^e - c). It learns every rule from the machine's own table, by direct simulation of a
visit, and falls back to direct simulation for anything without a rule. Checks: against a direct run of the machine
(every top-level visit of the first 3·10^7 steps, `py/vis_check.py`), against the same algorithm with exact integers
(`py/vis.py`, 1,500 rounds, same tape), and on the PR59 reference machine it halts in round 161,211 on `1011`, as PR59
proves. Result: rounds 1 to 161,210 use the four shared rules only; round 161,211 meets `1011` at the right end of
the word, rewrites it to `0001` and the run goes on. Observed: no halt and no visit to `111` up to round 200,000
(the run is still going; each further 100,000 rounds costs more than the last, the cost grows with the square).

A guess at how `1011` arises (not checked against the run): a count that dies exactly on a block leaves a stale
`110`; a later round whose blocks are aligned two cells earlier reads `0011`, writes `1011`, and comes again. Aligned
one cell earlier it would read `011` and then `111`. Nothing we know excludes a halt of this kind, and nothing proves one.

Tools (all in `../1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---/`): `py/visit.py MACHINE NAMESPACE OUT` writes
`lean/Visit.lean` by symbolic execution; `c/vis.c` (`gcc -O2 -o vis c/vis.c; ulimit -s unlimited; ./vis MACHINE [TOPVISITS [DUMP]]`,
two top-level visits per round for machines whose A1 is 0LB, one for A1 = 1LD); `py/vis.py`, `py/vis_check.py`.
<!-- F02-visit-law:end -->

<!-- T7-word-end:begin -->
## The word end: where the only junk comes from, and when it would be dangerous (22 November 2026)

**Proved in Lean (kernel), `lean/Word.lean`.** `visc f n w` makes `n` visits to the stream `w 0^∞` with exact counts,
one block at a time, by the rules of `lean/Visit.lean` (a digit block `000`/`100` passes every second visit on, a
doubler `1010` passes each visit on twice); `run f k` is the word after `k` rounds. `visc_sound` and `run_sound`: what
they compute is what the machine does (after `k` rounds the machine is at `0^∞ A> 1 0 w 0^∞`, after at least `k` steps,
and a `halt` result is a halt of the machine). `halts_of_run`: if some `run` reports `halt`, the machine halts from
blank tape. `not_halts_of_run`: if every number of rounds computes to a word, it never halts. So the question is
exactly whether the word computation ever meets `111`. `lean/WordRun.lean` (`native_decide`, about 5 s) evaluates
the first 2,000 rounds: no halt. (Round `k` sends 2^⌊k/2⌋ visits into the word, so 2,000 rounds are about 10^300
visits; that count is read off the rules, not part of the Lean statement.)

**The only junk is `11` (argument from the rules, checked on the run).** Every block a round writes is `000`, `100`
or `1010`, and each ends in `0`, so the part of the word a round has passed never has two `1`s side by side. A count
(the visits still travelling right) never runs out on a digit block or a doubler: a digit block passes at least one
visit on. It runs out only on a `0` with exactly one visit left, which writes a `1` in front of the cells it did not
reach. Every halting pattern, and `1011`, needs two touching `1`s, and the first pair can only come from such an end:
the count runs out on the last `0` of a digit block right before a block that starts with `1`. We call this a *junk
event*. The count is huge (2^e − c with e large, as in busycoq PR59) everywhere except in the last few dozen cells of
the word, so junk events can only happen at the word end; this is the "carry reaching the end of the tape" of the
earlier sections, and the stretches of `0101…` and `00100…` seen there are ordinary digit blocks and doublers read
with a different grid, not junk.

**When a junk event would be dangerous.** After a junk event the word ends `… 0 1 1 0^∞`, and the block just before
the `0 1 1` was written in the same round. Every block of a round starts 1 or 2 cells into a block of the round before
(busycoq PR59), so the next round meets either `0 0 1 1`: two visits give `0 0 0 1` through `1011` (`junk_offset1`),
harmless; or `0 1 1`: the second visit meets `111` and the machine halts (`junk_offset2_halts`). Which one is decided by the blocks the junk round wrote (PR59's phase rule): after a
`100` block the next round always enters at offset 2; after a `000` block it enters at offset 1 when the block before
is a doubler (which a round enters at offset 2, as PR59's run checks). The block before the junk passed exactly one visit on, so its count was 2 (it writes `000`) or 3 (it
writes `100`). A doubler always passes on an even count, so when the junk round writes doubler, digit, junk, the digit
is `000` and the next round is safe. Danger needs a count of exactly 3 in the digit block before the junk, which needs
a digit block (not a doubler) before that one too.

**The run (computed, not proved).** `c/wordrun.c` (in `../1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---/`; `./wordrun 0LF ROUNDS`) runs the same pass with
counts kept as 2^e − c: 300,000 rounds take about 8 minutes, 10^6 rounds about 1.5 hours. Checks: it halts the PR59
machines in round 161,211 on `1011`, as PR59 proves; its word after round 169,999 is, cell for cell, the tape of the
machine-level runner `c/vis.c` run on 1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA--- to the same point (1,055,794 cells);
and its first 2,000 rounds agree with `lean/WordRun.lean` and `py/vis.py`. Result: no halt and no `111` up to round
500,000. There are two junk events, in rounds 161,210 and 194,646, both on the cell just before the word's last `1`, both of the
safe kind: the junk round wrote doubler, `000` (count 2), junk, and the next round met `0 0 1 1` with 4 and 3 visits.
The two machines have the same run until a visit meets `111`, which has not happened.

**Next.** The counts that reach the last few blocks are small and exact, and the end of the word is a short list of
blocks fed by one small count per round. Decide whether a round can ever end digit, digit (count 3), junk: an
invariant of the word end that excludes it would prove that the machine never halts; a round that does it, followed
by a round that reaches the junk with two visits, is a halt.
<!-- T7-word-end:end -->

<!-- T8-end-invariant:begin -->
## No invariant of the word end alone, and how close the run comes (22 November 2026)

The section above ends on a question: is there an invariant of the last few blocks of the word that excludes "a digit
block that took exactly 3 visits, then junk `11`"? There is none: the danger is kept away by the exact size of the count that reaches the end,
which is carried in from the front of the word, not by the shape of the end. Both results below are computed, not
proved; they say where a proof cannot come from.

**The end on its own reaches the danger in 2 or 3 rounds** (`../1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---/py/endbfs.py K ROUND0 D`). Take the last K = 48 cells
of the real word after round ROUND0, with the block starts of the round that wrote them. Let every later round enter
the window 1 or 2 cells into a block of the round before (the PR59 phase rule) with any count of the form 2^a − d.
(At 48 cells before the end the run brings counts 2^a − d with a from 6 to 18 in nearly every round, and d is 0, 1,
2 or 4 in 96% of them.) Breadth-first search over those inputs, with counts that are exact powers of two (d = 0)
only, reaches `111` (for this machine a halt) after 3 rounds from the end of round 11 and of round 2,000 and after 2 rounds
from the end of round 5,000. The same model with the real counts gives the real next window in 98.5% of 200,000
rounds (the rest differ only in the first cells, where a block that starts left of the window overlaps it). So any
proof that the junk stays harmless has to say something about the counts, not only about the blocks at the end.

**One visit more and the run meets `111` two rounds later** (`../1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---/c/nearmiss.c 0LF`, checked on whole words by
`../1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---/py/nearmiss_check.py`). In each round r of the real run, change the count n at the first block start at least 60
cells before the word end, finish that round and run 6 more on a copy of the word end, the later rounds fed by the
real run's own exact count at a block start left of every changed cell. Over the first 500,000 rounds:

| change at 60 cells before the end | rounds after which a `111` follows within 6 rounds |
|---|---|
| n − 2, n − 1 | 0 |
| n + 1 | 47 |
| n + 2 | 105 |
| 2n | 15,526 |
| n / 2 | 10,524 |

With the same count the copy never leaves the real run (checked: 0 of 20,000 rounds), and every `111` met is
`11100`, the case with no proved rule. For 1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---, where every `111` halts, the
changes give the same counts in the first 200,000 rounds (`nearmiss 0LF`) except n / 2, 9,793 rounds against 4,223,
because there `11101` counts too.
The 152 misses by one or two visits fall in 142 rounds and all have the same shape: the real count is 2^a − 3,
2^a − 2 or 2^a − 1 (for example 8,190 at 59 cells before the end in round 798), one or two visits more make it
2^a − 1, 2^a or 2^a + 1, and exactly two rounds later the pass meets `111` (in the cases replayed on the whole word,
rounds 798, 834, 3,861 and 5,628: `111000` three cells before the end). `../1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---/py/nearmiss_check.py 798 1` replays that one on the whole word with exact
integers: round 800 meets `111000` at cell 4,867. Taking one or two visits away never led to `111`.

The run therefore comes within one or two visits of `111` about once every 3,500 rounds, and what keeps it
out is the low end of the count, 2^e − c with c the small deficit that busycoq PR59 tracks: it is set at the front
of the word, halves on every digit block and doubles on every doubler on its way to the end. A proof either way
needs a handle on that deficit along the whole word (for PR59 this is what the 161,211-round simulation supplies),
not an invariant of the last few blocks.
<!-- T8-end-invariant:end -->



## Events, third round

The reference's event theorems (`../1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---/py/events.py`) prove here unchanged (`lean/Events.lean`,
10 theorems). The differences: B1 = 0LF with F0 = 0LA = D0 (B1 followed by a 0 is the reference's B1 followed by D0),
D1 = 0RB (the reference's D1 = 0RF followed by F0 = 0RC = B0 on a 0), and E1 = 0RF: `L E> 1 0 R` → `L 1 B> 0 R` in 3
steps (`y_e1_detour`) where the reference takes 1. So the tape at every event is the reference's (2,000,000 events
compared), 2 steps later per use of E1 (498 = 2 · 249 at 2.95·10^8 steps). Here F1 halts after B1 or E1: the machine
halts if a B1 or an E1 is ever followed by a 1 (in the reference's run, B1 and E1 have always been followed by a 0).

## Status

Open. Lean, kernel only: the halting configurations and 10^4 steps (`lean/Blank.lean`), the sweeps of the run (`lean/Rules.lean`), the increments of both counters and the junk crossings, the reference's 9 theorems plus the E1 detour (`lean/Events.lean`). `native_decide`: 10^7 steps. C: no halt in
10^11 steps.

## Next steps

The last few blocks of the word cannot exclude the dangerous junk on their own (see "No invariant of the word end alone" above): the run stays safe because of the exact counts it brings to the end, and one visit more 60 cells before the end leads to `111` two rounds later in about one round in 3,500. Next: an invariant on the deficit c of the count 2^e − c along the whole word (the quantity busycoq PR59 follows), or a long run that meets `111`.

## Scripts

- `py/events.py` writes `lean/Events.lean` (`--coverage STEPS [SHOW]`: match every event of the run against the rules).
`py/rules.py` writes `lean/Rules.lean` (with `../1RB---_0LC0RB_1RA1LD_0RD1LE_1LF0LA_1LB0LE/py/g11rules.py`). The C
tools of the batch are in `../1RB---_0LC0RB_1RA1LD_0RD1LE_1LF0LA_1LB0LE/c/` (`gcc -O2 -o X X.c`): `ymax.c` (turns of
the busiest cell between end extensions), `chg.c` (change counts per cell between events), `usage.c` (transition
counts), `lockstep.c` (two machines side by side), `trlog.c` (every use of one transition), `longrun.c` (a long run).


## First look

Growth class **exp/exp** (left: exp, exponent 0.073; right: exp,
exponent 0.067). After 1,000,000,000 steps: 252 cells visited (88 left of the
start, 153 right), 74 ones.

- left, step 553,687,757: `B>0 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0^4 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^4 1 0^2 1 0 1 0^4 1 `
- left, step 810,905,821: `B>0 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^4 1 0^2 1 0 1 0^4 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0^7 1 0 1 0^`
- right, step 551,601,124: `1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^3 1 0^3 1 0 1 0 1 0^3 1 0^3 1 0 1 0 1 0^3 1 0^3 1 0^3 1 0^3 1 0^3 1 0^3 1 0^3 1 0^3 1 0^3 1 0^3 1^2 0 1 0 1 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1 0 1 0 1 0^3 1 0^3 1 0 1 0 1^2 0 1^2 0 1 0 1 0 1^2 0 1^2 0 1 0 1 0 1^2 0 1^2 0 `
- right, step 946,793,053: `1 0 1 0^3 1 0 1 0 1 0 1 0 1 0^3 1 0^3 1 0^3 1 0^3 1 0^3 1 0 1 0 1 0 1 0 1 0^3 1 0^3 1 0^3 1 0^3 1 0 1 0 1 0^3 1 0^3 1 0^3 1 0^3 1 0^3 1 0^3 1 0 1 0 1 0^3 1^2 0 1 0 1 0 1^2 0 1^2 0 1 0 1 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1 0 1 0 1 0^3 1 0 1 0 1^2 0 1^2 0 1^2 0 1 0^3 1^2 0 1^2 0 1 0 1 0 1^2 `

## Pages

- [`pages/holdouts/1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---/explainer.html`](../../pages/holdouts/1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---/explainer.html)
- [`pages/holdouts/1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---/proof-status.html`](../../pages/holdouts/1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---`](../1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---/README.md): 9,999,705 configurations, the last at step 10,000,000 here and step 9,999,704 there
- [`1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---`](../1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---/README.md): 9,999,705 configurations, the last at step 10,000,000 here and step 9,999,704 there
- [`1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---`](../1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---/README.md): 8,749,930 configurations, the last at step 9,999,389 here and step 9,999,999 there
- [`1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---`](../1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/README.md): 7,916,289 configurations, the last at step 10,000,000 here and step 9,165,962 there

<!-- end of related machines -->
