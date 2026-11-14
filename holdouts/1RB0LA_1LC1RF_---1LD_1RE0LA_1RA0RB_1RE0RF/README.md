# 1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF

bbchallenge id 169745. One of the six-state holdouts whose halting from blank tape is open. Family: **counter of 110 blocks with a messy right end**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LA |
| B | 1LC | 1RF |
| C | --- | 1LD |
| D | 1RE | 0LA |
| E | 1RA | 0RB |
| F | 1RE | 0RF |

## Status

Open. Lean (kernel): two shift rules of a round (`lean/Rules.lean`, from `py/rules.py`); generated: halting
configurations, no halt in 10^4 steps (kernel) and 10^7 (`native_decide`). C: no halt in 10^9 steps.

## What it does

At each time the head is at the left end in state A on `A>0 0`, the tape is `0 0 (110)^p ...` and p has
gone up by exactly 1 since the previous time: 671 times up to 10^9 steps, p from 2 (step 52) to 672 (step
997,776,132). A round costs ≈ 10.1·p² steps, so p ≈ (0.3 t)^(1/3). After the counter comes `0^3` (p ≡ 0, 2 mod 3)
or `0 1 1` (p ≡ 1), then a second run `(110)^q` (q = 629 at the end), then 20–30 disordered cells. The width grows by 6
in 556 of 670 rounds (3,943 at the end). `py/counter.py` checks this on a `tmrun ... at A L` log.

Halting: C on a 0, entered only from B on a 0, which comes from E on a 1 when the cell to its right is 0: a halt
is exactly `E>1 0`. Lean proves the sweep `E> (110)^n` → `(011)^n E>` and the zigzag
`(011)^n A> 0 0` → `A> 0 0 (011)^n`. Odd runs of 1s do occur away from the head (lengths 1, 3, 5, all states,
both sides), and the tail at returns has 658 shapes in 667 returns, so the invariant must locate the odd runs; no
closed tape language was found (windows ≤ 8 cells with parity flags, learned DFAs). In 10^9 steps E reads a 1 only as `E>1 1 0` (123,762,963 times) or `E>1 1 1 1 0`
(429,985 times), never a lone 1, also in the disordered right end (`py/ecensus.c`). No finite-automata-reduction
certificate with up to 7 DFA states on the left or 8 on the right, and no conserved linear quantity mod 2..12.

## Later

1. The two inner steps of a round are proved (`sweep`, `carry`); prove the rest of the round, then the whole round from `A>0 0 (110)^p` by induction, assuming a fixed shape of the right end.
2. The disordered right end is not finite-state as seen (658 shapes in 667 returns): look for a regular language
   that contains its shapes and says where its odd runs of 1s sit.
3. Prove the parity fact `py/ecensus.c` sees (E only ever on an even run of 1s): that alone rules out `E>1 0`.

## First look

Growth class **power/power** (left: power, exponent 0.325; right: power,
exponent 0.333). After 1,000,000,000 steps: 3,948 cells visited (1,097 left of the
start, 2,106 right), 2,621 ones.

- left, step 970,729,436: `A>0 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 `
- left, step 988,723,786: `A>0 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 `
- right, step 975,610,659: `1 0 1^2 0 1 0^2 1 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 `
- right, step 993,969,263: `1 0 1^2 0 1^2 0 1 0^2 1 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 0 1^2 `

## Accelerated run (13 November 2026)

Observed, not proved: the accelerated simulator `rsim.py` ran 2.41x10^9 steps from blank tape without reaching a halting transition. Its tape, state and head position were equal to those of a plain C simulator at 4 checkpoints, the last at 1.00x10^9 steps. No trip-level jump was used in this run, only the shift rules over repeated words (exact by induction, but the program is not verified).

```sh
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF 400
```

## Pages

- [`pages/holdouts/1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF/explainer.html`](../../pages/holdouts/1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF/explainer.html)
- [`pages/holdouts/1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF/proof-status.html`](../../pages/holdouts/1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF/lean/check.sh
gcc -O2 -o /tmp/tmrun tools/c/tmrun.c && /tmp/tmrun 1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF 1000000000 at A L 100000 > /tmp/al.txt
python3 holdouts/1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF/py/counter.py /tmp/al.txt
gcc -O2 -o /tmp/ecensus holdouts/1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF/py/ecensus.c && /tmp/ecensus 1000000000
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC`](../1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC/README.md): rename A→C, B→D, C→E, D→F, E→B, F→A; it is this table started in state F

<!-- end of related machines -->
