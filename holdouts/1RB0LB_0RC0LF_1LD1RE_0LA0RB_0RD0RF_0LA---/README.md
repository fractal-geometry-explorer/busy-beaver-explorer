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

Decode what a carry writes when it reaches the end of the tape, so that the junk after each visit is a formula in the
counters; then decide whether a carry can ever find a 1 where it has always found a 0.

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
