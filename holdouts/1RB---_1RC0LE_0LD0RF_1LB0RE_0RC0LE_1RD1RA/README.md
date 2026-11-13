# 1RB---_1RC0LE_0LD0RF_1LB0RE_0RC0LE_1RD1RA

bbchallenge id 139516. One of the six-state holdouts whose halting from blank tape is open (group G11, family **two-ended counter, (10)^n left / 110 digits right**). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 1RC | 0LE |
| C | 0LD | 0RF |
| D | 1LB | 0RE |
| E | 0RC | 0LE |
| F | 1RD | 1RA |

## Status

Open. Lean (kernel): the halting configurations and bounded runs (`lean/Blank.lean`), the halt from `C> 1 1 1` (`halt_ctx`; that every halt passes through it is from the table)
and shift rules (`lean/Rules.lean`), 183 event rules for all sizes (`lean/Events.lean`). C: no halt in 10^11 steps.

## What it does

An **event** is the head in state D on cell 75 (cells from the start cell; 47,619,048 visits in steps 10^9-2·10^9).
From step 6.2·10^8 on the tape at an event is

    ... [left] D> c1 c2 0 [R] ...

- `left`: binary, 4-cell digits `0001` = 0, `0101` = 1, lowest digit next to the head;
- `c1 c2`: a phase, `00`, `10`, `01`, `11` = 0, 1, 2, 3;
- `R`: base 3, 3-cell digits `010` = 0, `110` = 1, `100` = 2, lowest digit first.

Each event moves the phase on by one. 0->1 and 2->3 add 1 to `left` (12n+8 steps, n carried ones); 1->2 adds 1 to
`left` and 1 to `R` (12k+12n+32 steps, k carried 2s); 3->0 changes nothing else (4 steps). So every 4 events add 3 to
`left` and 1 to `R`: after n phase cycles the left side holds 3n (+ a constant) in binary and the right side n in base
3. Example, events 20,505,785-20,505,795 (steps 1,000,000,037-1,000,000,285): the lowest three left digits go 000,
001, 010, 011, 011, 100, 101, 110, 110, 111, 000; R's lowest digit 2, 2, 0 (carry), 0, 0, 0, 1, 1, 1, 1, 2.

R gets a new digit at events 2·3^k+1 (55, 163, 487, ..., 86,093,443). The left counter's overflows send the head to
the left end (events 1,972, 71,015, 2,556,528 = steps 35,863,455, 153,303,963, 623,065,849; 2 new cells each time;
ratio about 36, so the next is near event 9.2·10^7, step ~3·10^9) and change the layout: from 1.5·10^8 to 6.2·10^8 the
junk word `0110 1101` sits between the head and `left`.

**Proved** (`lean/Events.lean`, kernel): the seven counter rules for every size (`t_ph01`, `t_ph23`, `t_ph30`,
`t_ph12_r0`, `t_ph12_r1`, `t_ph12_c_r0`, `t_ph12_c_r1`) and 176 rarer events mined from the run (`py/mined.txt`).

**Coverage** (3·10^9 steps, `evcov` with `c/rules.txt`): 92,035,010 events; the seven rules match 90,117,609
(97.9%), all 183 rules all but 158,814 (99.83%; the rest: events of the 1.5-6.2·10^8 layout and reorganizations).

**Where it can halt.** From `C> 1 1 1` it halts (Lean `halt_ctx`); every halt passes through it (from the table). In 3·10^9 steps C has `1 1` ahead 9 times: 7 before the first event
(steps 37 to 590,829) and 2 in uncovered events (step 2,425,727 at cell 45; step 153,303,845 at cell 63, the sweep of
the left-end visit at event 71,014). Never inside a proved rule. It follows (not as a theorem) that halting is a question about the sweeps of the
left-end visits.

## Files

- `py/events.py` writes `lean/Events.lean` and `c/rules.txt` (`python3 py/events.py lean|cov`); `py/mined.txt`.
- The batch tools in `../1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/`: `c/evcov.c` (coverage, `./evcov M 3000000000
  75 D c/rules.txt 0 0 C:11`), `py/miner.py`, `py/autoev.py`, `c/ev.c`, `c/busy.c`, `c/ctxcount.c`, `c/forbid.c`.
- `lean/rules.py` writes `lean/Rules.lean`.

## Next steps

Decode the left-end visit (what the sweep writes, the ratio of ~36 between visits) and prove it as a rule; then the
run is two counters plus one reorganization rule, and halting asks whether a sweep can give C three 1s.

## Pages

- [`pages/holdouts/1RB---_1RC0LE_0LD0RF_1LB0RE_0RC0LE_1RD1RA/explainer.html`](../../pages/holdouts/1RB---_1RC0LE_0LD0RF_1LB0RE_0RC0LE_1RD1RA/explainer.html)
- [`pages/holdouts/1RB---_1RC0LE_0LD0RF_1LB0RE_0RC0LE_1RD1RA/proof-status.html`](../../pages/holdouts/1RB---_1RC0LE_0LD0RF_1LB0RE_0RC0LE_1RD1RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB---_1RC0LE_0LD0RF_1LB0RE_0RC0LE_1RD1RA/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB---_1RC0LE_0LD0RF_1LB0RE_0RC0LE_1RD1RA 100000000000
gcc -O2 -o ctxcount holdouts/1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c/ctxcount.c && ./ctxcount 1RB---_1RC0LE_0LD0RF_1LB0RE_0RC0LE_1RD1RA 1e10 C 3
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC1RF_1RA---`](../1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC1RF_1RA---/README.md): rename A→F, B→A, C→B, D→C, E→D, F→E; it is this table started in state B

<!-- end of related machines -->
