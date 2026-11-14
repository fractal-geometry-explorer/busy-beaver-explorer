# 1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---

bbchallenge id 32161. A six-state bbchallenge holdout (group G11). **It halts from blank tape**: Lean theorem `halts_from_blank` (kernel, plus `native_decide` for the run of a verified checker), see "It halts" below.

Family **G11-Y** (two counters ticking together, `1RB0LB_0RC0LD` and relatives): this machine is a relative in different clothes: its left counter has 4-cell digits `x011`, its left-end extensions come after exactly 3·2^k turns of the busiest cell, each count twice, and at its left-end visits the tape is that of the reference family: at step 14,008,454 its 183-cell tape agrees with that of 1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA--- at step 9,617,068 in all cells but the first two.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LB |
| B | 0RC | 0LE |
| C | 1RD | 0RF |
| D | 1LB | 1RB |
| E | 0LA | 0RE |
| F | 1RE | --- |

## What it does

The tape is, most of the time, `L · engine · R`. Every visit of the head to the engine (an *event*) adds 1 to two binary
counters, one on each side. In the reference machine `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---`, `L` is in 4-cell blocks (`0101` = 1,
`0001` = 0, lowest digit next to the engine) and `R` has one cell per digit, three cells apart (cells 9, 12, 15, … right
of the head), lowest digit nearest the engine. Between some digits of `R` there are fixed stretches (junk) that the carries cross.

- **Left side: clockwork.** When `L` overflows the carry reaches the left end, the tape grows by two cells and `L`
  restarts. The busiest cell (the lowest digit of `L`) turns 3·2^k times between consecutive left-end extensions, each count twice: 48, 96, 96, 192, 192, …, 3·2^22
  (first 1.5·10^9 steps, `ymax.c`).
- **The junk.** The change counts per cell (`chg.c`: how often each cell changes between consecutive events over a
  whole period) halve from one digit to the next, with junk stretches between some digits. The junk is written when a
  carry reaches the end of the tape (at irregular event counts); how is not decoded.
- **Where it can halt.** Only in F reading 1; F is entered from C1 (0RF) only. After C1, used about 2.9·10^7 times in 10^9 steps, the head has read a 0 every time (F0 is used exactly as often). Unlike the other members this machine has no rare transition: every transition is used more than 10^7 times in 10^9 steps. Halting would need that ordinary step to find a 1.

The family: `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---` (reference), `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---` (the same run, checked cell for cell for
10^10 steps), `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---`, `1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---`,
`1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---` (left-end extensions after 2^k events, each twice, within a few hundred
steps of each other), `1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---` and `1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---` (same
right part at the left-end visits, 3·2^k), and the mirror case `1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---`.

<!-- F02-halt:begin -->
## It halts: the visit law and a verified checker (F02, 13 November 2026)

**Theorem `halts_from_blank` (`lean/Halt.lean`): the machine halts from blank tape.** Everything is checked by the
Lean kernel except the evaluation of a checker that is itself proved correct; that evaluation is by `native_decide`
(compiled code, so the theorem also depends on eleven `native_decide` axioms, one per evaluation). The number of steps is not computed;
it is astronomically large (the halt is in round 161,211, and the number of visits in a round grows exponentially with the round).

**The visit law (kernel), `lean/Visit.lean`.** A *visit*: the head stands on a 0 (the lead cell) with a 0 on its left
and a stream `s` on its right, in state C (form `V`) or in state F (form `W`); it comes back in state A two cells
further left, both 0s restored and `s` rewritten to `v(s)`. For every stream `s` and every tape to the left:

| stream | after the visit | theorem (form V) |
|---|---|---|
| `0 s` | `1 s` | `V_0` |
| `100 s` | `000 v(s)` | `V_100` |
| `110 s` | `000 v(s)` | `V_110` |
| `1010 s` | `1010 v(v(s))`, the first nested visit in form W | `V_1010` |
| `1011 s` | the machine halts | `V_1011_halts` |

In this machine form W obeys the rules for `0`, `100`, `1010` and `1011` (`W_0`, `W_100`, `W_1010`, `W_1011_halts`)
but not the one for `110`: `W` turns `1100 s` into `1010 v(s)` (`W_1100`), and `1101`, `111` have no rule of this
shape. The first nested visit of the `1010` rule is a W visit, so the law below is only claimed when the
stream behind a `1010` block does not start with `11`. Lean proves that this never matters after the
first two visits to a stream (`av2_guard`), and the checker tests it wherever it applies the rule.
If a nested visit halts, so does the visit around it (`V_100_halts_1`, `V_1010_halts_1`, `V_1010_halts_2`, ...).
The run is a sequence of rounds (`start`, `round`, `round_halts`): after 6 steps the tape is `0^inf A> 1 0 0 S_1`
with `S_1 = 1 0^inf`, and a round turns `0^inf A> 1 0 0 S` into `0^inf A> 1 0 0 S'` with `S' = v(1 0 S)` (a V visit).

**The abstract system (kernel), `../1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---/lean/VisitLaw.lean`.** The four rewriting rules and the halting pattern as
inductive relations `AV`, `AH` on streams, with no machine in them; the `1010` rule carries the guard "the stream
behind does not start with `11`". `Law` lists what a machine's `V` and `W` must satisfy; `Law.av`, `Law.ah` turn
abstract visits into machine visits. Count laws: under n visits `000 r` and `100 r` are binary digits that pass
every second visit on (`law_Z`, `law_H`, `law_G`), `1010 r` passes 2n visits on (`vs_L`), and the same for "one
of the first n visits halts" (`hvs_Z`, `hvs_H`, `hvs_G`, `hvs_L`, `hvs_X`).

**The checker (kernel), `../1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---/lean/VisitCheck.lean`.** `scan` carries a count of visits through a finite word in one
pass; the count is kept as a pair e, c that stands for 2^e - c, so astronomically many visits cost one step per cell.
`scan_sound`, `hscan_sound`: what it returns is what the abstract system does. `check k w`: run k rounds from the
word w, then find a halting visit in the next round. `lean/Law.lean`: this machine satisfies `Law`, and
`halts_of_check_blank : check k [true] = true -> HaltsFromBlank` (axioms: the three standard ones).

**The evaluation (native), `../1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---/lean/VisitRun.lean`.** `check_run : check 161210 [true] = true`: rounds 1 to 161,210
use the four rewriting rules only and round 161,211 meets `1011`. The run is cut into ten segments
(`../1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---/lean/VisitSeg1.lean` to `VisitSeg10.lean`), each "k rounds take the word after a rounds to the word after b
rounds" by `native_decide`, chained by `iter_add` (`../1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---/lean/VisitSeg.lean`, kernel); the words at the boundaries
(up to a million cells) are written as numbers in `../1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---/lean/VisitW*.lean`. The last word has 1,001,253 cells.
`lean/check_halt.sh` compiles the checker to native code and checks everything; the segments took 10 to 30
minutes each, about 3 hours of computing in all. Each segment was checked once (13 and 14 November 2026);
the whole check was then run again from start to end on a fresh clone on 14 November 2026 for the twin
(the commands of `check_halt.sh`, with the ten segments four at a time, about 40 minutes on four cores), and this
machine's `Halt.lean` was compiled against those segments; both printed `HALT CHECKED`.
The repository's automatic checks run `check.sh` (the kernel-only part) but not `check_halt.sh`.

**The same law as the machines of busycoq PR59.** `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---` and its two relatives obey
this law with one form of visit (entered one cell further left), and PR59 proves in Rocq that they halt in round
161,211. The Lean proof here does not use PR59; that both land on the same round is a cross-check (as is our C
simulator `../1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---/c/vis.c`, which halts in that round on the PR59 machine).
The twin `1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---` halts in the same round by the same checker run; that is a
separate theorem about a different table, not a consequence of this one.

Tools: `../1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---/py/visit2.py MACHINE NAMESPACE OUT` writes `lean/Visit.lean` by symbolic execution of the table.
`../1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---/lean/VisitGen.lean` (run with the compiled checker) writes the word after k more rounds; `visit_chain.sh` and
`visit_segments.py` next to `visit2.py` produced the boundary words and the segment files (they carry the paths of the
machine they were run on).
**Also in Coq (14 November 2026).** `tools/coq/busycoq/VisitLaw2/`: `halts : halts tm c0` on busycoq's definitions, Coq 8.20.1, no axioms. It uses the checker of busycoq PR59 extended to two forms of visit, with the whole run as one `vm_compute` of about 15 minutes; see the README there.
<!-- F02-halt:end -->

## Events, third round

The same two counters as the reference `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---`, in other words: left digits `0110` = 0, `0111` = 1
next to the block `011001`; on the right the phase cell, the block `001010000` and the right counter one cell per digit,
three cells apart, with junk units `1010000` between digits, exactly the reference's right side. `lean/Events.lean`
(6 theorems, every size): the left increment (22n+34 steps), the right increments (42; 6k+48), and carries across
junk units. Coverage: 95.5% of the 879,588 events of the first 10^8 steps (right1 92,325 and junk_jk 1,733 times, the
same counts as in the reference).

## Status

**Halts** (Lean, level native): `halts_from_blank` in `lean/Halt.lean`, by the visit law and a verified checker (see "It halts" above). Kernel only: the visit law in two forms (`lean/Visit.lean`), the abstract system and the checker with its correctness proof, and `halts_of_check_blank` (`lean/Law.lean`). Older results, all kernel: the halting configurations and 10^4 steps (`lean/Blank.lean`), the sweeps (`lean/Rules.lean`), the left-and-right increments (`lean/Events.lean`). The sections below on counters and junk are the earlier description of the same run and are kept for the record.

## Next steps

None needed for the halting question. Open ends: the number of steps to the halt (the checker does not count them), and a proof of the evaluation inside the kernel (it is about 10^11 list operations, too many for kernel reduction).

## Scripts

- `py/events.py` writes `lean/Events.lean` (`--coverage STEPS [SHOW]`: match every event of the run against the rules).
`py/rules.py` writes `lean/Rules.lean` (with `../1RB---_0LC0RB_1RA1LD_0RD1LE_1LF0LA_1LB0LE/py/g11rules.py`). The C
tools of the batch are in `../1RB---_0LC0RB_1RA1LD_0RD1LE_1LF0LA_1LB0LE/c/` (`gcc -O2 -o X X.c`): `ymax.c` (turns of
the busiest cell between end extensions), `chg.c` (change counts per cell between events), `usage.c` (transition
counts), `lockstep.c` (two machines side by side), `trlog.c` (every use of one transition), `longrun.c` (a long run).


## First look

Growth class **exp/exp** (left: exp, exponent 0.075; right: exp,
exponent 0.067). After 1,000,000,000 steps: 248 cells visited (86 left of the
start, 149 right), 98 ones.

- left, step 579,891,093: `B>0 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^4 1 0^26 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0^4 1 0^2 1 0^2 1 0 1 0 1 0^2 1 0 1 0^4 1 0^2 1 0 1 0^4 1 0^5 1`
- left, step 804,526,293: `B>0 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^2 1 0 1 0^4 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^4 1 0^2 1 0 1 0^4 1 `
- right, step 745,351,313: `1 0 1^3 0 1^2 0^2 1^3 0 1^3 0 1^3 0 1^3 0 1^2 0^2 1^2 0^2 1^3 0 1^2 0^2 1^2 0^2 1^3 0 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0 1^3 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^3 0 1^2 0^2 1^2 0^2 1^3 0 1^2 0 1^2 0 1^3 0 1^2 0 1^2 0 1^3 0 1^2 `
- right, step 801,510,397: `1 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^2 0^2 1^2 0^2 1^3 0 1^2 0^2 1^2 0^2 1^3 0 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0^2 1^2 0 1^3 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^3 0 1^2 0^2 1^2 0^2 1^3 0 1^2 0 1^2 0 1^3 0 1^2 0 1^2 0 1^3 0 1^2 0 `

## Pages

- [`pages/holdouts/1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---/explainer.html`](../../pages/holdouts/1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---/explainer.html)
- [`pages/holdouts/1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---/proof-status.html`](../../pages/holdouts/1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---/lean/check.sh
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---`](../1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---/README.md): 9,132,095 configurations, the last at step 10,000,000 here and step 9,132,094 there

<!-- end of related machines -->
