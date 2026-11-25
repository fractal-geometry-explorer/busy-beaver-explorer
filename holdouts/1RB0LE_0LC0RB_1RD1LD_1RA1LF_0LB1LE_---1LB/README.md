# 1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB

bbchallenge id 38215. One of the six-state holdouts whose halting from blank tape is open (group G11, family **clock and word map (block grows by 3 at the left end)**; first called the fuel-block counter).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 0LC | 0RB |
| C | 1RD | 1LD |
| D | 1RA | 1LF |
| E | 0LB | 1LE |
| F | --- | 1LB |

## What it does

**The clock.** One step before every visit of the left end in state E the tape is `E>1 1^(3+3k) 0 W`: a block
`1^(4+3k)` and a word W of short blocks. Write `J(k, W)` for `1^(4+3k) 0 W` (head in E on its first cell). The tick

    L 0 0 0 E> J(k, W)   ->   L E> J(k+1, W')      W' = P^(2^k)(W)

is, for every k, the sweep (`0^3 E> 1^(4+3k) 0` -> `1 1 1 0^(3+3k) 1 1 A>`, 3k + 13 steps), one P-step (a trip
into the word, `L 0^3 1 1 A> W` -> `L E> 1^4 0 W'`), the ticks 0, ..., k-1 (each eats three of the 0s), and the
merge (`1 1 1 E> 1` -> `E> 1 1 1 1`, 3 steps). So tick k makes 2^k trips into the word, each applying one fixed
map P, and takes `E + 19·2^k − 3` steps (E the time in the trips). **Proved in Lean for every k and every word,
under the hypothesis that the 2^k trips all return** (`PChain`). The hypothesis is met by the real run: the 15
trips of the four ticks after step 470 are proved for the actual words, and the theorem then takes the run from
blank tape exactly to step 2,964 (`run_ticks`). (The earlier clock test, from block 13 at step 123,063, is the same
statement with P replaced by P^8.)

**Phases.** A phase lasts while every trip returns. It ends when a trip runs off the left of its region: the
unfinished ticks are abandoned, the block is partly taken apart, and a new phase starts from a somewhat shorter
block with a longer word. Exact accelerated run (`clock.py`, phases with a final block of 30 or more):

| phase starts at step | block | last tick at step | block | word cells |
|---|---|---|---|---|
| 471 | 1^4 | 68,467 | 1^34 | 31 |
| 121,828 | 1^10 | 4.187·10^9 | 1^82 | 66 |
| 5.655·10^9 | 1^52 | 2.332·10^15 | 1^139 | 109 |
| 2.378·10^15 | 1^121 | 1.541·10^22 | 1^208 | 140 |
| 2.332·10^22 | 1^205 | 2.612·10^23 | 1^220 | 148 |
| 3.495·10^23 | 1^184 | 5.516·10^29 | 1^283 | 195 |
| 7.590·10^29 | 1^271 | 4.226·10^33 | 1^322 | 216 |
| 5.305·10^33 | 1^319 | 7.069·10^34 | 1^334 | 224 |
| 9.524·10^34 | 1^319 | 3.762·10^37 | 1^361 | 248 |
| 5.294·10^37 | 1^349 | 2.833·10^41 | 1^400 | 267 |
| 3.549·10^41 | 1^397 | 1.345·10^42 | 1^406 | 273 |
| 1.799·10^42 | 1^373 | 6.846·10^45 | 1^442 | 315 |
| 6.921·10^45 | 1^421 | 4.375·10^50 | 1^490 | 347 |
| 4.415·10^50 | 1^463 | 2.976·10^55 | 1^535 | 383 |

The run was followed through 65 phases (seven of them in the first 500 steps) to 6.04·10^187 steps; the last
phase followed ended with the block 1^1858 and a word of 1,240 cells. No halt. The phase ends do not follow an
evident formula: from step 121,828 on the new block is shorter than the last one of the phase before by 3 to 66 cells.

**A clock inside the word** (22 Nov). A trip does not always stay short. When the word starts with
`0 1^(4+3k) 0 Z`, the trip's first pass turns the block into `0^(3+3k)` and goes on into `Z`. The tape it leaves is
exactly the one the sweep of tick k leaves, with the trip's own `0 0 0` as the zeros left of the block. From there on
the trip is tick k of a second clock, and its own trips go into `Z`. If those 2^k trips return, the trip reaches

    L 0 0 0 1 1 A> 0 1^(4+3k) 0 Z   ->   L 0 0 0 E> 1^(4+3(k+1)) 0 Z'

in E + 19·2^k − 8 steps, where E is the time of the 2^k nested trips. That is the start of tick
k+1 of the nested clock. **Proved in Lean for every k, Z and L** (`nest`, `lean/Nest.lean`), and checked against
plain simulation on 1,117 random cases. The nested clock then keeps ticking in the trip's place (`nest_then_tick`) and
eats zeros of whatever lies to its left. Words hold clocks, and those clocks hold clocks in turn.

This is why the trips cannot be listed. Enumerate words cell by cell, stopping a prefix once the trip returns, exits
or halts without reading further. The number of prefixes still undecided grows by about 1.7 per cell: 129 at length
10, 2,956 at length 16 and 70,941 at length 22 (`../R02-clock-word/py/trip_tree.py`). No decided trip halts, and the
exits are the five seen before. So "every trip returns or exits in one of five ways" is a statement about nested
clocks of every depth, not a finite check.

**Trips by the residue of the first block** (25 Nov). The same first pass works for a block of any length:
`L 0 0 0 1 1 A> 0 1^j 0 Z` becomes `L 0 0 0 1 1 1 0^(j-1) 1 1 A> Z` in j + 4 steps (`enter_gen`). For j ≥ 4 the trip
into Z and the ticks of the nested clock then eat the 0s three at a time, and what is left over decides the end.
Suppose the trips into Z return, 2^m of them taking Z to Z'. Then:

| j | left over | the trip reaches | Lean |
|---|---|---|---|
| 4 + 3k | nothing | `L 0 0 0 E> 1^(7+3k) 0 Z'`, tick k+1 of the nested clock | `nest` |
| 5 + 3m | one 0 | `L 0 0 0 E> 1^4 0 1^(3+3m) 0 Z'`, tick 0 of a nested clock; its one trip, into `1 1 1 ...`, returns, and the head leaves with `1^7 0 1 0 1^(1+3m) 0 Z'` | `trip_res2`, `res2_leaves` |
| 6 + 3m | two 0s | `L E> 0 1 1 0 1 1 0 0 1^(4+3m) 0 Z'`, and the next step leaves in state B | `trip_res0`, `res0_leaves` |

All three are proved for every m, Z and L (`lean/Residue.lean`) and agree with plain simulation on 899 random words.
So, as long as the trips into Z return, a trip into a word that starts with `0 1^j 0` (j ≥ 4) never returns. It
leaves its region to the left, and only the case j = 4 + 3k goes on as a clock there. Two of the five exits seen in
testing are explained this way: B011011 (j ≡ 0 mod 3) and E111111 (j ≡ 1 or 2 mod 3, the nested clock of j = 4 + 3k once its tick k+1 is done).

**Halting.** The only halting transition is F on 0 (`step_none_iff`); F is entered only from D on 1 (1LF, from the
table), so the machine halts exactly when D reads a 1 whose left neighbour is a 0. A tick whose trips all return is
proved to finish, so a halt can only come at a phase end. Open: a closed form for P^(2^k) on the words that occur,
what a phase end builds, and whether one ever halts.

**Earlier observations.** The word starts `1^3 0 1^M` (M the "fuel block" 21 → 15 → 9 → 27 in the first phases);
`bbtools.ctl` with windows of 7 cells closes but allows a halt (followed by `110010`, `110011` or `110111`); K = 8
does not close in 100 rounds.

## Status

Open.

- Lean, kernel (`lean/Clock.lean`): `tick` (every k, every word, under `PChain`), `tick_left_end`; rules
  `rule_sweep`, `rule_merge` in `lean/ClockRules.lean` (written by `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/gen_clock.py`).
- Lean, kernel (`lean/Nest.lean`): `nest`, a trip into `0 1^(4+3k) 0 Z` becomes tick k+1 of a nested clock
  (every k, Z, L, under `PChain` for the nested trips); `enter`, `after_sweep`, `nest_then_tick`.
- Lean, kernel (`lean/Residue.lean`): `trip_res2`, `res2_leaves`, `trip_res0`, `res0_leaves`, the trips into
  `0 1^(5+3m) 0 Z` and `0 1^(6+3m) 0 Z`; `enter_gen` (the first pass for every block length), `rule_r1`, `rule_r2`,
  `pstep_11` (P(1 1 X) = 1 0 X for every X).
- Lean, kernel (`lean/Instance.lean`): `run_ticks`, the run from blank tape through four ticks (steps 470 to 2,964)
  via `tick_left_end` with the 15 trips proved concretely.
- Lean (`lean/Rules.lean`): shift rules `bclear`, `ewalk`; (`lean/Blank.lean`) `step_none_iff`, no halt in 10^4
  steps (kernel) and 10^7 (`native_decide`).
- Trusted: `clock.py` agrees with `tools/c/tmrun.c` at all 50 visits in the first 10^10 steps (`tmcheck`), and
  follows the run to 6.04·10^187 steps without a halt.

## Scripts

- `python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py 1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB tmcheck 1e10` — compare with `tmrun` at every visit (about a minute).
- `python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py 1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB run 187` — the phases (about 25 minutes to 10^187).
- `python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/gen_clock.py 1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB` — writes `lean/ClockRules.lean` and `lean/Clock.lean`.
- `python3 holdouts/R02-clock-word/py/trip_tree.py 16`: trips decided by a prefix of the word, and how many prefixes stay undecided.
- `python3 holdouts/1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB/py/instance.py 1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB 470 4` — writes `lean/Instance.lean`.
- `py/phases.py LOG` prints the events of a `tmrun MACHINE T at E L 400 > LOG` log.

- Invariant searches that forget the word (22 Nov, `../R02-clock-word/far/`): there is no left automaton with up
  to 7 states for which the least right automaton closes. The same holds for windows of the last 10 cells plus the
  position mod 3 (3,073 states), and for the trip alone with its left wall. See `../R02-clock-word/README.md`.

## Next steps

A proof that doesn't depend on the word has to follow nested clocks: a trip is either short or a clock whose phases
end in the same five exits. The trips that start with a block are now classified by its residue (above), given that
their own trips return. What remains is a trip whose nested trips exit, and the trips that start with `1` or with a
short block (j ≤ 3). The next step is the phase end of a nested clock, with an arbitrary word after it and an
arbitrary stack before it. Separately: describe P^(2^k) on the words of the run in closed form, accelerate a phase
end, and read off the map from one phase to the next.

## Pages

- [`pages/holdouts/1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB/explainer.html`](../../pages/holdouts/1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB/explainer.html)
- [`pages/holdouts/1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB/proof-status.html`](../../pages/holdouts/1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB/lean/check.sh
python3 holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/clock.py 1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB tmcheck 1e10
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1LB_1RC1LE_1RD0LF_0LA0RD_---1LD_0LD1LF`](../1RB1LB_1RC1LE_1RD0LF_0LA0RD_---1LD_0LD1LF/README.md): rename A→C, B→D, C→A, D→B, E→F, F→E; it is this table started in state C

<!-- end of related machines -->
