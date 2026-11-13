# 1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA

bbchallenge id 77294. A six-state holdout of BB(6), first of a family of six starting `1RB0RB` (holdout indices
31–36). **Open.** The machine runs in *epochs*: each epoch is a base-4 countdown whose length is exponential in the
length of the counter it starts with, and it can only halt at the end of an epoch, when a residue condition holds.
Epoch 3 starts at step 589,506 (proved in Lean) and lasts about 3.6·10^26 excursions (≈10^53 steps, extrapolated);
simulator experiments predict that it ends without halting and that epoch 4 does not halt either, but epoch 4 is a
countdown of length about 4^(3·10^25), and what happens after it is out of reach.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RB |
| B | 0LC | 1RA |
| C | 1RD | 1LC |
| D | 1LA | 1LE |
| E | 1LF | 0LD |
| F | --- | 0LA |

The three machines 31–33 of the family (`1RB0RB_0LC1RA_…`, `1RB0RB_1LC1RA_0LE1LD_…`, `1RB0RB_1LC1RA_0LF0LD_…`) are
distinct machines (not equal up to mirror image and renaming of states); they share `A = 1RB 0RB` and `B1 = 1RA`,
so all of them flip pairs `x 1` on every right sweep (`11 ↔ 01`), and the tapes of all three are made of blocks of
1s separated by single 0s. Beyond that their left-going parts differ and so do their behaviours.

## What it does

**The tape.** Every time the head stands in state A on the blank cell right of the tape (the start of an
*excursion*) the tape is a word of blocks of 1s separated by *single* 0s. The only halting transition is F on 0, and
it is reached exactly from `0 0 D> 1` (theorem `halt_00`: D on a 1 writes 1 and goes left in E, E on 0 goes left in
F, F reads 0). In every run we made, a D/E pass inside the tape always meets a single 0 (the `0 0` that the zigzag
rounds write is right of the head and is gone before a pass comes back), so the machine can halt only at the *left
end*: when a D/E pass runs through the leftmost (lead) block and hits the blank tape. This is observed, not proved. Then (`lead_odd`, `lead_even`):

* lead block odd, `0^∞ 1^(2a+1)` with D on its right end: **halt** after 2a + 2 steps;
* lead block even, `0 0 1^(2a+2)`: the pass turns into a right sweep and the tape gains one cell on the left
  (a *left record*).

**One excursion** (theorems in `lean/Rules.lean`, all for every value of the variables and every surrounding
tape): B turns at the right end and a D/E pass crosses the last block (`tail_odd`, `tail_even`, `de_pass`: each
`1 1` becomes `0 1`), then the head zigzags left in rounds of 8 + 2j cells, rewriting `0101 01 1^(2j)` as
`00 1101 1^(2j) 10` (`zig_1`) or `0101 1^(2j) 01` as `00 1101 (01)^j 10` (`zig_2`), until the word left of the head
fits neither pattern; it then comes back right in rounds `1111 X 10 → 0101 X' 01` (`ret_d`, `ret_b`, X a run of `11`
or `01` pairs, X' the run flipped) and a final A/B sweep (`sweep_d`, `sweep_b`) to the right end. Each excursion
adds one pair `1 0` at the right end of the tape, which is why the right end grows like √steps.

**Epochs.** Between two left records the depth of the excursions counts down: most excursions turn shallow, and
one in four goes deeper by a fixed amount, like the digits of a base-4 counter. The left records (epoch ends) come at
steps 7,165, 586,215 and 589,506 (the short epoch 1, epoch 2 with 495 excursions, and a three-excursion transition);
`epoch3_start` (`lean/Epoch3.lean`, `native_decide`) proves that after 589,506 steps the tape is

    0^∞ P (0 1)^520 A> 0^∞,    P = 1^4 0 1 0 1 0 1^3 … (106 cells, lean/Epoch3.lean)

**The epoch-3 law** (simulator, `py/epochs.py`). Start the machine on `P (01)^m` and let E(m) be the number of
excursions until the next left record. Then

* E(m + 12) = 4 E(m) + 2 for every m from 12 to 87 (checked: `python3 py/epochs.py law 12,13,…,75`);
* for m ≡ 4 (mod 12), m = 4 + 12t: E = (14·4^t − 2)/3 (t = 1, 2, 3, 4: 18, 74, 298, 1194), and the epoch ends
  without a halt in the configuration `core (10)^(E+1) 1 1 0` with the core 24 cells longer for each t;
* the real run has m = 520, t = 43: E = 361,065,844,791,569,246,845,577,898 ≈ 3.6·10^26 excursions, about 10^53
  steps, ending (by the same law) with N = E + 1 ≡ 7 (mod 12) trailing pairs (N mod 12 cycles 7, 3, 11 with t).

**Epoch 4** (simulator). Take the end-of-epoch-3 configuration for t = 1…4 and replace its N trailing pairs by
N₂ ∈ {1, …, 30}: the next epoch halts exactly when N₂ ≡ 2 (mod 12) (t ≥ 2; for t = 1, N₂ ≡ 8, 10), and otherwise ends
in another left record after E₄ excursions with E₄(N₂ + 12) = 4 E₄(N₂) + 2 (`python3 py/epochs.py epoch4 16,28,40,52
1,2,…,30`). Since the real N ≡ 7 (mod 12), the prediction is that epoch 4 does not halt; it lasts about 4^(N/12) ≈
4^(3·10^25) excursions, and its end configuration again has the form core (10)^N′ tail. Whether epoch 5 halts depends
on N′ modulo a period that nobody has computed: the run is a tower of countdowns with a residue test at each level.

## Status

Open. Proved: the moves of an excursion (kernel), the only way to halt (`halt_00`, with `step_none_iff`), the
halting and non-halting outcome at the left end (`lead_odd`, `lead_even`), and the start of epoch 3 (native). Not
proved: that every excursion decomposes into these moves (the tape grammar), and the epoch laws, which are
extrapolations of simulator runs. The macro simulator `c/mrun.c` (blocks of 2 cells, run-length coded, 128-bit step
counter) ran 10^18 steps from blank without a halt, still inside epoch 3.

## What is proved

| result | level | where |
|---|---|---|
| halts exactly when F reads 0 | kernel | `step_none_iff`, `lean/Blank.lean` |
| no halt in 10^4 / 10^7 steps | kernel / native | `blank_runs_kernel`, `blank_runs_native` |
| the moves of an excursion (12 rules, all values, any context) | kernel | `lean/Rules.lean`, generated by `py/gen_rules.py` |
| `0 0 D> 1` halts in two steps; a pass into an odd lead block halts, into an even one extends the tape | kernel | `halt_00`, `lead_odd`, `lead_even` |
| after 589,506 steps the tape is `P (01)^520 A>` | native | `epoch3_start`, `lean/Epoch3.lean` |
| no halt in 10^18 steps | trusted | `c/mrun.c` (`./mrun <M> 2 1e18 0`) |
| E(m+12) = 4E(m)+2 for epoch 3 (m = 12…87), the m ≡ 4 formula, epoch-4 residues | trusted (finite runs) / heuristic (extrapolation to m = 520) | `py/epochs.py` |

## For later

* Prove the tape grammar (blocks separated by single 0s) and the excursion as one macro step on the block word;
  then the base-4 law of an epoch can be stated as a theorem about that word, as in the finished holdouts.
* Derive E(m + 12) = 4E(m) + 2 symbolically (it is visibly a counter: 12 more pairs = one more base-4 digit).
* Work out the period of the residue test one level up (how N′ at the end of epoch 4 depends on N) to say whether
  epoch 5 can halt.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA/lean/check.sh
python3 holdouts/1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA/py/epochs.py law 12,16,20
python3 holdouts/1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA/py/epochs.py epoch4 16,28 1,2,7,14
```

## Pages

- [`pages/holdouts/1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA/explainer.html`](../../pages/holdouts/1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA/explainer.html)
- [`pages/holdouts/1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA/proof-status.html`](../../pages/holdouts/1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA/proof-status.html)
