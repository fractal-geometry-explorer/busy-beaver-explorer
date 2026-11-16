# 1RB1LD_1LC0RD_0LA0RB_0LE1LF_1RF0LC_0RB---

bbchallenge id 11545. One of the six-state holdouts whose halting from blank tape is open. Family: **mixed-radix word counter: ternary words 110, binary words 10 / 1000, slowly growing left prefix (rule not found)**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LD |
| B | 1LC | 0RD |
| C | 0LA | 0RB |
| D | 0LE | 1LF |
| E | 1RF | 0LC |
| F | 0RB | --- |

## What it does

**Extensions of the left end.** Each time the head reaches a new cell at the left end it is in state C and the tape reads
`C>0 0^2 1 0 (1^2 0)^m V`, with V a word of the tokens `1 0`, `1^2 0` and `0^3 1`; two more cells follow within 12
steps. m goes up and down (it fell 14 times in 10^11 steps), and V changes along its whole length between extensions.
The last seven extensions came at 1.5, 3.2, 8.1, 23, 36, 43 and 65 billion steps (ratios 1.2 to 2.8), so this is not
a binary counter. The machine halts only in state F reading a 1.

**A counter in two bases.** Cut the tape into words `1^a 0^b`; only `10`, `110`, `1000` and `11000` occur. Between
two extensions (steps 230,340,555 to 249,136,554) count how often the head crosses the left edge of each word going
right (`py/visits.py`, output `py/visits_2.3e8.txt`):

    left end   0, 2, 12, 44, 142, 430, 1294, 3645, 10935, 32805, 98415      ×3 per 110 word
               29524, 14762, 7381                                            ×1/2 per binary word pair
               ×5/2, then 18455, 55365, 166095, 498285                       ×3 per 110 word (the busiest point)
               149485, 74743, ... ×5/2, ×3/10, ×3/5 at junctions, ... 2, 1   ×1/2 per binary pair, to the right end

A base-b digit is passed b times as rarely as its neighbour on the busy side, so this is the visit profile of a
counter whose digits are the words: base 3 for `110`, base 2 for the pairs of `10` / `1000`, counting outwards from a
busiest point in the middle of the tape. The turn counts confirm the left block: from step 3,083,613 to 3,258,424 the
head turns at cells 5, 8, …, 20 from the left end 25, 75, 225, 675, 2025, 6075 times. The left end grows when the
base-3 block next to it overflows. The junction factors 5/2, 3/10 and 3/5 (exact to three decimals) are where words of
one base become the other; their rule is what is missing, and it is why the extensions come at irregular times.

## What is established

**Proved in Lean, kernel only** (`lean/Blank.lean`): the halting configurations (`step_none_iff`); no halt in 10,000
steps (`blank_runs_kernel`).

**Proved in Lean with `native_decide`**: no halt in 10^7 steps (`blank_runs_native`).

**Computed** (trusted C): no halt in 10^11 steps (`tools/c/tmrun.c`; 262 cells, 203 left and 59 right of the start,
115 ones). All 61 left extensions have the shape above.

**Heuristic**: the width grows like the logarithm of the step count, at irregular times; the visit profile of a
mixed-radix counter (above).

**Open**: the rule at the junctions (how a block of one base turns into the other), when the left end moves, and the
question.

The closed-tape-language search (`bbtools.ctl`, K up to 6, and K = 8 on the mirrored machine) finds no closed set, so
the halt is not confined to an edge.

## Status

Open, no macro rule proved. Kernel: halting configurations, no halt in 10,000 steps; native: no halt in 10^7 steps;
trusted: no halt in 10^11 steps. The counter reading is heuristic (measured on two stretches of the run).

## How far it was run

Direct simulation to 10^11 steps (`tools/c/tmrun.c`, earlier pass); there is no accelerated simulator, since the rule
at the junctions is not known. `bbtools.listframe` was tried as a first decider of structure: its case table of
head-turn frames keeps growing (115, 124, 137 cases after 10^5, 10^6, 4·10^6 steps), so the run is not a finite
frame map at that resolution.

## Open questions

* Read the words as digits with the bases above and find the value they encode at each extension; check whether
  one tick of the busiest point adds 1 to it, and what the junctions do (5/2, 3/10 and 3/5 suggest a Collatz-like
  rule with factors 3/2 and 5/2).
* Find the event at which the busiest point moves, and a macro rule between such events.

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | the machine, the halting configurations and bounded runs (generated) |
| `py/visits.py`, `py/visits_2.3e8.txt` | crossings of every word between two steps, and their ratios |

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LD_1LC0RD_0LA0RB_0LE1LF_1RF0LC_0RB---/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB1LD_1LC0RD_0LA0RB_0LE1LF_1RF0LC_0RB--- 100000000000 records 100000
python3 holdouts/1RB1LD_1LC0RD_0LA0RB_0LE1LF_1RF0LC_0RB---/py/visits.py 230340600 249136500
```

## Pages

- [`pages/holdouts/1RB1LD_1LC0RD_0LA0RB_0LE1LF_1RF0LC_0RB---/explainer.html`](../../pages/holdouts/1RB1LD_1LC0RD_0LA0RB_0LE1LF_1RF0LC_0RB---/explainer.html)
- [`pages/holdouts/1RB1LD_1LC0RD_0LA0RB_0LE1LF_1RF0LC_0RB---/proof-status.html`](../../pages/holdouts/1RB1LD_1LC0RD_0LA0RB_0LE1LF_1RF0LC_0RB---/proof-status.html)
