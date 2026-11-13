# 1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD

> **13 November 2026: proved by others, not yet independently rebuilt.** Hubert Chilczuk published a complete
> Rocq proof that this machine never halts (`Theorem nonhalt`, busycoq, repo
> `hubertchilczuk/BB6-1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD`, head 830debc). It closes a finite set of 385
> (engine pattern, remainder, parity) nodes with the stack size left free, so the epoch map below is *not*
> Collatz-hard; our closure search failed because it tracked residues of the stack size and used an unsound
> threshold. Our spot checks agree with it (start node at step 226,258,281, two engine cycles). The Rocq build
> (~225 CPU-hours) has not been rebuilt here, so `decision` stays `open`. The closure search in `py/decide/` is
> stopped.

bbchallenge id 31480. One of the six-state holdouts whose halting from blank tape is open (group G09: the visited tape grows like the square root of the step count on both sides).

**What it does.** An exponential counter with epochs. At every left crossing of the stack the tape is an engine *P*, a stack of n identical 20-cell half-units `U = 10101010101010101110`, a junction, a block of m words `V = 1011101110` (10 cells), and a fixed tail. The engine eats the stack from its **left** end (not the right end, as an earlier version of this note said) and falls into one of three exact cycles: 1,744 round trips per 100 half-units, 704 per 40, or 2,336 per 132; every round trip adds exactly one V. When the stack is empty the block is re-read as the next stack, one half-unit per two V's, so n' = (R/2C)·n + O(1) with R/C the cycle of the epoch: n' ≈ 8.72 n, 8.80 n or 8.85 n. Which cycle the next epoch takes depends on residues of n and on the junction left over, a Collatz-like dependence. An exact accelerated simulation (Python, symbolic) follows 30 epochs, to about 7·10^61 steps, without a halt. The sweep rules, the shift rules of an epoch transition, one engine lemma and the right part of a round trip are proved in Lean. Decision: open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RE |
| B | 1LC | 0LB |
| C | 1RD | 0LB |
| D | 1RF | 0LA |
| E | 1RC | --- |
| F | 0RA | 0LD |

## The three parts

`c/snap.c` prints the tape at visits to one end; `py/epochs.py` splits it (from the repository root):

```sh
gcc -O2 -o /tmp/snap holdouts/1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD/c/snap.c
/tmp/snap 1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD 40000000000 300 R | python3 holdouts/1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD/py/epochs.py
```

At every visit to the right end (outside the conversions) the tape is

    P  U^N  1101110  V^m  1101110010110        U = (10101010101010101011)^2,  V = 1101110101

| visit | step | width | P | N | m |
|---|---|---|---|---|---|
| 84 | 451,035 | 1,100 | 38 | 21 | 16 |
| 200 | 2,606,636 | 2,665 | 133 | 14 | 193 |
| 480 | 13,977,238 | 6,269 | 117 | 3 | 599 |
| 640 | 25,255,535 | 8,392 | 90 | 165 | 166 |
| 1,200 | 91,682,381 | 15,868 | 166 | 140 | 1,008 |
| 3,600 | 808,222,835 | 47,700 | 98 | 38 | 4,604 |
| 4,800 | 1,437,426,910 | 63,457 | 125 | 1,469 | 451 |
| 25,200 | 39,707,461,047 | 333,402 | 180 | 595 | 30,938 |

## Epochs, first look (from the direct simulation)

- The leftward sweep crosses the block and the stack word by word (`left_V`, `left_U`: B and C complement them, almost), the rightward sweep restores
  them (`right_V`, `right_U`). These rules hold for every N and m.
- Within an epoch, a unit disappears about every 23.5 visits to the right end (the junction `1101110` alternates with a half-converted unit
  while it happens; the units are in fact eaten at the left end, see below; counted in checkpoints, 34.9 round trips per 40-cell unit) and m grows by about 1.5 per round trip (the right end grows 7 or 14 cells a visit). So a unit is worth
  about 35 words of the block: 350 cells for 40.
- When N reaches 0 the block of V's is converted into units, 4 V's (40 cells) per unit, by a front that takes about a hundred round trips; the
  engine then starts on the new stack. Epoch 0 builds 85 V's, epoch 1 has 21 units (85/4), epoch 2 has 165, epoch 3 about 1,490; each is about 8.8
  times the last, and the time per epoch grows about 80-fold (the tape is 8.8 times wider and is swept 8.8 times more often). Epoch 3 should end near
  10^11 steps, with about 13,000 units for epoch 4.

## The exact round trip (`py/decide/`)

`py/decide/fs.py` is a symbolic simulator: the tape is a list of literal cells and blocks `(w)^k`, k a linear form in up to 8 variables; a block
is crossed by a shift rule found by simulating one copy (the head carries a short word across), blocks are rotated and regrouped
(`(w)^2k = (ww)^k`), and a run stops with an error whenever it would need a copy that a block's symbolic count does not guarantee. A halt
raises `Halted`. Every round trip is split at the *checkpoint* (the leftward sweep has just crossed the stack):

- **E lemma** (`decide.E`): engine, stack `(U)^x+c` and an unknown context to its right; runs until the restoring sweep reaches the context.
  Memoized by (engine, state, prefix, word). The run is symbolic in x ≥ 0, so it holds for every stack of at least c half-units; it is then
  re-run at the smallest c (0, 1, 2, ... 256) for which the result is the same, and that c is the lemma's threshold. (An earlier version trusted
  a threshold read off the unrolls without re-running, which is unsound: some shift rules use a copy without unrolling it. At epoch 10 that
  produced a negative stack; the BFS log below was made with that version.)
- **X lemma** (`decide.X`): the stack's far end, the junction, the V block, the tail, with an unknown context to the left; symbolic in every
  block count y_k ≥ need_k, re-run at the needs.

`py/decide/epochsim.py` chains the lemmas round trip by round trip from a real configuration at step 449,234,410 (`py/decide/real4000.txt`,
written by `c/dump.c`; 156 half-units left in that epoch, 3,215 V's). When the (engine, state, prefix, word, block shape) key repeats it has
found the cycle; it measures one more period and jumps q periods at once, all counts moving linearly, as long as the stack and every shrinking
block stay above the thresholds of the lemmas used in the period. When the stack runs out (no E lemma at the current count) it composes the
tape and runs the epoch transition in full, symbolically, until a new stack of at least 40 half-units appears.

```sh
cd holdouts/1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD/py/decide
python3 epochsim.py real4000.txt 30 449234410      # about 9 minutes, one core; output as in epochsim30.log
```

## The epochs

Within an epoch the engine part of a round trip depends only on the engine and the first few half-units; the
right part only lengthens the V block by one word. The engine settles into one of three cycles of engine contents:

| cycle | round trips | half-units eaten | V words added | n'/n |
|---|---|---|---|---|
| A | 1,744 | 100 | 1,744 | 8.72 |
| B | 704 | 40 | 704 | 8.80 |
| C | 2,336 | 132 | 2,336 | 8.85 |

At the end of the epoch one leftward sweep complements the block (V to `0101010111`, then `1010001000` after the next pass), and about 30
round trips later it is regrouped in pairs into the new stack; the transition's shift rules are `conv_r0` .. `conv_l8` in `lean/Epoch.lean`.
A short junction is left between the new stack and the new (empty) V block: `01000`, `0001000101000` or `1010101010001000101000`, followed by a
block `(1010001000)^j` with j between 4 and 631 in the 30 epochs. Which cycle the next epoch falls into, and the next junction, depend on
the residue of n modulo the cycle's consumption and on parities: the map on (n, junction, j) is an affine map per residue class, of the
Collatz type. It has not been enumerated completely (see the BFS below).

Exact run from step 449,234,410 (`py/decide/epochsim30.log`; stack sizes in half-units; the step count of a jumped stretch is summed in closed
form from two measured periods):

| epoch | ends at step | stack | next stack | ratio | cycle | junction of the next stack |
|---|---|---|---|---|---|---|
| 0 | 1.2314e09 | 156 | 2964 | 19.0 | (partial epoch) | `0001000101000 (1010001000)^30` |
| 1 | 9.4844e10 | 2964 | 25887 | 8.734 |  | `1010101010001000101000 (1010001000)^14` |
| 2 | 7.2083e12 | 25887 | 225793 | 8.722 |  | `01000 (1010001000)^5` |
| 3 | 5.4834e14 | 225793 | 1968918 | 8.72 | A | `01000 (1010001000)^36` |
| 4 | 4.1698e16 | 1968918 | 17168970 | 8.72 | A | `0001000101000 (1010001000)^42` |
| 5 | 3.2043e18 | 17168970 | 151086944 | 8.8 | B | `1010101010001000101000 (1010001000)^24` |
| 6 | 2.4812e20 | 151086944 | 1329565164 | 8.8 | B | `1010101010001000101000 (1010001000)^5` |
| 7 | 1.9012e22 | 1329565164 | 11593808210 | 8.72 | A | `01000 (1010001000)^68` |
| 8 | 1.4458e24 | 11593808210 | 101098007663 | 8.72 | A | `0001000101000 (1010001000)^18` |
| 9 | 1.1110e26 | 101098007663 | 889662467426 | 8.8 | B | `01000 (1010001000)^46` |
| 10 | 8.6031e27 | 889662467426 | 7829029713730 | 8.8 | B | `01000 (1010001000)^22` (via a 46-half-unit stack made from the left-over block `(1010101000)^93`) |
| 12 | 6.5922e29 | 7829029713730 | 68269139103753 | 8.72 | A | `1010101010001000101000 (1010001000)^70` |
| 13 | 5.0131e31 | 68269139103753 | 595306892984787 | 8.72 | A | `1010101010001000101000 (1010001000)^25` |
| 14 | 3.8119e33 | 595306892984787 | 5191076106827345 | 8.72 | A | `01000 (1010001000)^23` |
| 15 | 2.9293e35 | 5191076106827345 | 45681469740080969 | 8.8 | B | `01000 (1010001000)^6` |
| 16 | 2.2682e37 | 45681469740080969 | 401996933712712549 | 8.8 | B | `01000 (1010001000)^59` |
| 17 | 1.7565e39 | 401996933712712549 | 3537573016671870414 | 8.8 | B | `0001000101000 (1010001000)^631` |
| 18 | 1.3459e41 | 3537573016671870414 | 30847636705378710376 | 8.72 | A | `0001000101000 (1010001000)^35` |
| 19 | 1.0235e43 | 30847636705378710376 | 268991392070902354511 | 8.72 | A | `1010101010001000101000 (1010001000)^47` |
| 20 | 7.8654e44 | 268991392070902354511 | 2367124250223940719760 | 8.8 | B | `1010101010001000101000 (1010001000)^5` |
| 21 | 6.0264e46 | 2367124250223940719760 | 20641323461952763076299 | 8.72 | A | `01000 (1010001000)^10` |
| 22 | 4.5828e48 | 20641323461952763076299 | 179992340588228094025369 | 8.72 | A | `01000 (1010001000)^49` |
| 23 | 3.5810e50 | 179992340588228094025369 | 1592659498538260710769951 | 8.848 | C | `01000 (1010001000)^64` |
| 24 | 2.7283e52 | 1592659498538260710769951 | 13887990827253633397913991 | 8.72 | A | `01000 (1010001000)^4` |
| 25 | 2.0966e54 | 13887990827253633397913991 | 122214319279831973901643296 | 8.8 | B | `01000 (1010001000)^30` |
| 26 | 1.6064e56 | 122214319279831973901643296 | 1065708864120134812422329603 | 8.72 | A | `01000 (1010001000)^21` |
| 27 | 1.2346e58 | 1065708864120134812422329603 | 9378238004257186349316500722 | 8.8 | B | `01000 (1010001000)^13` |
| 28 | 9.5597e59 | 9378238004257186349316500722 | 82528494437463239873985206438 | 8.8 | B | `01000 (1010001000)^11` |
| 29 | 7.3252e61 | 82528494437463239873985206438 | 719648471494679451701151000187 | 8.72 | A | `1010101010001000101000 (1010001000)^38` |

No round trip, jump or transition in the 30 epochs halts: about 7.3·10^61 steps. Epochs 0 and 1 agree with the direct simulation of
`c/snap.c` (1,469 40-cell units at step 1,437,426,910 and 595 at step 39,707,461,047, both inside epoch 1).

## Towards a proof: the closure search (`py/decide/bfs.py`)

`bfs.py` keeps the epoch symbolic: from an entry class (engine, state, word, junction shape, the junction counts, the V count up to parity,
lower bounds) it finds the cycle with a huge stack, then for every residue of n modulo the consumption of a period it computes the stack end
and runs the transition symbolically (V count `2t + B`), giving new entry classes. If the set of classes closed up with no halt, that would
prove non-halting (at the level of this Python code). The partial run in `py/decide/bfs_partial.log` (made with the unsound threshold above,
so heuristic only) handled 121 transitions and 118 entry classes without a halt and without closing: each class has 40 to 132 residues, the
junction counts take many values, and the queue grows faster than it is processed (about 6 transitions a minute). A closure would need many
thousands of transitions and a C implementation, or a coarser abstraction of the junction.

## Lean (`lean/Epoch.lean`)

Generated by `py/decide/gen_lean.py` with `bbtools.symtm`, kernel-checked (`rfl` segments and the shared shift-rule lemmas), for all values of
the counts:

- `conv_r0`, `conv_l1`, ..., `conv_l8`: the nine shift rules of the epoch transition (`py/decide/leanrules.out`, collected by `leanrules.py`), e.g.
  `conv_r4`: D carries `00101011` across `(1000101000)^n` and leaves `(0101010111)^n`, 70 steps a copy; the rightward rules take 52 to 136 steps
  a copy, the leftward ones 10 or 20.
- `engine_step n R`: one E lemma of cycle A, 116·n + 929 steps, the rest of the tape untouched.
- `right_part m n L`: the X lemma of a round trip, symbolic in the V count m and the stack n, 62·m + 20·n + 120 steps, adding one V.

These are single lemmas; the cycles (thousands of E lemmas) and the transitions are checked only by the Python code.

## Sweep rules (`lean/Rules.lean`)

Generated by `py/rules.py` with `tools/py/bbtools/symtm.py` (carried words up to 40 cells: the rightward sweep over the stack backs up into the units it has just restored); every rule holds for all values of `n` and every tape `L`, `R`, with the exact step count.

| rule | from | to | steps |
|---|---|---|---|
| `erase` | `L 1^n B> 1 R` | `L B> 1 (0)^n R` | n |
| `left_V` | `L (1101110101)^n B> 1 R` | `L B> 1 (0100010100)^n R` | 10 · n |
| `left_U` | `L (10101010101010101011)^n C> 1 R` | `L C> 1 (10101010101010101000)^n R` | 20 · n |
| `right_U` | `L 0 1 0 1 0 1 0 1 0 1 1 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 1 1 0 0 1 0 1 0 1 0 1 0 1 0 1 C> 0 0 1 0 1 0 1 0 (00101010101010101010)^n+3 R` | `L 0 1 0 1 0 1 0 1 0 1 1 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 1 1 (01010101010101010111)^n+3 0 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 1 1 F> R` | 116 · n + 368 |
| `right_V` | `L 1 D> (0010101011)^n R` | `L 1 (1011101011)^n D> R` | 30 · n |

## Status

Open. Lean, kernel only: the halting configurations, no halt in 10,000 steps (`lean/Blank.lean`), the sweep rules (`lean/Rules.lean`), the
transition's shift rules, one engine lemma and the right part of a round trip (`lean/Epoch.lean`). Lean with `native_decide`: no halt in 10^7
steps. C: no halt in 4·10^10 steps. Python, symbolic and exact: no halt in 30 epochs, about 7·10^61 steps. Not proved: that every epoch, for
every residue, ends in a configuration of the same family. The epoch map looks Collatz-like (affine per residue class, the class of the next
epoch chosen by residues of the current one), so a proof needs the class enumeration to close, which the partial search has not shown.


## First look

Growth class **sqrt/sqrt** (left: sqrt, exponent 0.51; right: sqrt,
exponent 0.497). After 1,000,000,000 steps: 53,148 cells visited (8,090 left of the
start, 30,709 right), 35,933 ones.

- left, step 977,079,927: `C>0 1 0 1 0^3 1 0 1 0^3 1 0 1 0 1 0^3 1 0^3 1 0^3 1 0 1^2 0^3 1 0 1 0^3 1 0^3 1 0 1 0 1 0 1 0^3 1 0^3 1 0 1 0 1 0 1 0^3 1 0^3 1 0^3 1 0^3 1 0 1 0 1 0^3 1 0 1 0 1 0^3 1 0^3 1 0^3 1 0^3 1 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 `
- left, step 992,802,291: `C>0 1 0 1 0^3 1 0 1 0 1 0 1 0^3 1 0^3 1 0^3 1 0 1^2 0^3 1 0^3 1 0 1 0^3 1 0^3 1 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0^3 1 0^3 1 0^3 1 0^3 1 0 1 0 1 0^3 1 0 1 0 1 0 1 0^3 1 0^3 1 0^3 1 0^3 1 0 1 0 1 0^3 1 0^3 1 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^3 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0^3 1 0 1 0 1 0 `
- right, step 973,441,834: `0 1 0 1^3 0^2 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^3 0 1 0 1^3 0^2 1 0 1 0 1 0 1 0 1^3 0 1 0 1^3 0 1 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1^3 0 1^3 0 1^3 0 1 0 1 0 1 0 1 0 1^3 0 1^3 0 1 0 1 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^3 0 1 0 `
- right, step 989,135,354: `0 1 0 1^3 0 1 0 1^3 0^2 1 0 1 0 1 0 1 0 1^3 0 1 0 1 0 1 0 1^3 0 1 0 1 0 1^3 0 1^3 0 1^3 0 1 0 1^3 0 1^3 0 1 0 1 0 1^3 0 1^3 0^2 1 0 1 0 1 0 1 0 1^3 0 1 0 1^3 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^3 0 1 0 1^3 0 1^3 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1^3 0 1 0 1 0 1 0 1 0 1 0 1 0 `

## Pages

- [`pages/holdouts/1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD/explainer.html`](../../pages/holdouts/1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD/explainer.html)
- [`pages/holdouts/1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD/proof-status.html`](../../pages/holdouts/1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD/lean/check.sh
python3 holdouts/1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD/py/rules.py | diff - holdouts/1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD/lean/Rules.lean
(cd holdouts/1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD/py/decide && python3 gen_lean.py) | diff - holdouts/1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD/lean/Epoch.lean
(cd holdouts/1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD/py/decide && python3 epochsim.py real4000.txt 30 449234410)   # ~9 min; compare with epochsim30.log
```

`py/decide/real4000.txt` is the configuration at step 449,234,410 printed by `c/dump.c` (`gcc -O2 -o dump c/dump.c && ./dump 100000 0 4 0 0 4000`).
