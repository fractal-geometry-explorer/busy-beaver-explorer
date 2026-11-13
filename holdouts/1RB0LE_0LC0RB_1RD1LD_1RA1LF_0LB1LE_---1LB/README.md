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
- `python3 holdouts/1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB/py/instance.py 1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB 470 4` — writes `lean/Instance.lean`.
- `py/phases.py LOG` prints the events of a `tmrun MACHINE T at E L 400 > LOG` log.

## Next steps

Describe P^(2^k) on the words of the run in closed form, accelerate a phase end, and read off the map from one
phase to the next.

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
