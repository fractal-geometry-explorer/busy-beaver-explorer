# 1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC

bbchallenge id 135376. One of the six-state holdouts whose halting from blank tape is open. **Its rounds act on
a list of blocks of 1s by a recursive base-6 digit rule, now written down completely (computed; checked against
direct simulation on thousands of block lists, part of it proved in Lean): even blocks grow by 5/2, odd blocks are
divided by 6 digit by digit, and a round halts only when a digit recursion runs off the end of a number. The orbit
from blank tape never has more than two blocks; the map has been iterated for 1,000,000 rounds without a halt.**

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RD |
| B | 1LC | 0RD |
| C | 1RF | 1RB |
| D | 1LE | 0RA |
| E | 0LB | 0LE |
| F | --- | 0RC |

## What it does

A *round start* is the head in state B at the left end of the tape, which is a list of blocks of 1s:

    (a, b, c, …)  =  B> 0 0 1^a 0 1^b 0 1^c …          E n = (n)

One step later the tape is a **phase state** with `i = 0`, `x = a`, `R = (b, c, …)`:

    P(i, x, R)  =  w^i C> 0 1 0 1^x 0 R            w = 10101

A round is a walk through phase states. Each `w` becomes five 1s when the round ends, so `i` counts fives.

**T1, odd `x ≥ 7`** (Lean, `odd_sweep`, `odd_sweep_new`, for every tape on both sides): one sweep takes six 1s off
the block, writes a `w` and adds one to the next block (or makes a new block of one 1):

    P(i, x, y:R)  →  P(i + 1, x − 6, (y+1):R)

So an odd block is divided by 6: after `q = ⌊x/6⌋` sweeps the next block has grown by `q` and `x mod 6 ∈ {1, 3, 5}` is
left.

**T3, even `x ≥ 2`**: the block is rewritten as `w 0 (01)^k 0`, then a whole **nested round** runs on the blocks `R`
to its right, and its first result block `B0` is merged into what is left of `x`:

    P(i, x, R)  →  P(i + 1, x − 2 + B0, B')        B0:B' = nested round on R   (0 and nothing if R is empty)

With nothing on the right this is the proved even sweep `x → x − 2` (`pass`), which gives `n ↦ 5n/2 + 1`. One
exception: at top level `P(i, 2, y:R') → P(i, y + 3, R')`.

**Ends.** When `x` is 0, 1, 3 or 5 the round (top level or nested) ends; "`c +` round" adds `c` to the first block of
that round's result:

| `x` left | top level | nested |
|---|---|---|
| 0 | `5i + 1` (only with `R` empty; `(0, …)` itself halts) | `5i` if `R` is empty, else `5i +` nested round on `(y+1):R'` |
| 1 | **halts** if `R` is empty, else `5i + 2 +` top-level round on `R` | `5i` if `R` is empty, else `(5i + y) : R'` |
| 3 | `(5i + 6 + y) : R'` (`5i + 6` if `R` is empty) | `5i : (y+1) : R'` (`5i : 1` if `R` is empty) |
| 5 | `(5i + 6) : (y+1) : R'` | **halts** if `R` is empty, else `5i + 7 +` nested round on `(y−1):R'` |

(`R = y:R'`.) The top-level ends 2 (`end2`), 3 (`end3`, `end3_new`), 5 (`end5`, `end5_new`) and the halt at 1
(`halt1`) are Lean theorems for every `i`, `y` and tape to the right. The nested rules, the exception and so the map
as a whole are **computed**: `py/roundmap.py check` compares the map with direct simulation (`c/evc.c`) on random
lists of up to six blocks (more than 15,000 lists tried, blocks up to 3000): no mismatch.

**One block.** For a single block the recursion unrolls to the table found earlier: write
`n = 6^j · m + (6^j − 1)/5` with `m ≢ 1 (mod 6)` (`j` trailing base-6 digits 1). Each trailing digit 1 is a top-level
end with `x = 1`, which hands the rest of the number, `⌊n/6⌋`, to a new round:

| `m` | next round start |
|---|---|
| `0` (n = 0, 1, 7, 43, 259, …, base-6 repunits) | **halts** |
| even, `m > 0` | `E (n + 3m/2 + 1 + j)` |
| `m ≡ 3 (mod 6)` | `E (n + 3 + j)` |
| `m = 6q + 5` | two blocks `(n − q + 1 + j, q + 1)` |

**Two blocks.** `(a, b)` with `a` odd is the same with `b` added to the quotient. With `a` even the second block is
run as a nested round first (`T3`): for even `b` it comes back as `5b/2`, so `(a, b) → P(1, a − 2 + 5b/2, ())`; for
`b = 6t + 3` as `5t` and a new block `t + 1`; for `b = 6t + 1` as `6t`; for `b = 6t + 5` as `5t + 7 +` the nested round
on `t − 1`, which **halts for `b = 5`** (and `b = 41, 257, …`: `t − 1` again of that form down to `t = 0`). A round
that starts with at most two blocks ends with at most two (every case of the table), so the orbit from blank tape
stays in one or two blocks.

**From blank tape** (`py/roundmap.py orbit`; the first 18 rounds agree with direct simulation, 3.4·10¹⁰ steps):

    E 2 → E 6 → E 16 → E 41 → (36, 7) → E 106 → E 266 → E 666 → E 1666 → E 4166 → E 10416 → E 26041
        → E 32553 → E 32556 → E 81391 → (79133, 2261) → (65946, 15450) → E 130718 → E 326796 → E 816991
        → E 851035 → (827398, 23640) → E 2216246 → …

Each round costs about `n²` steps (a sweep crosses the block), so the tape grows like the square root of the step
count on the right, and the left end barely moves. That is the exp/sqrt shape the triage saw.

## Does it halt?

Open: the machine halts from blank tape exactly when the orbit of `(2)` under the round map reaches a halting
round, if the computed map is right (it is not yet a Lean theorem as a whole).

* **Proved (Lean, kernel):** `even_round` (every even round `E (2p+4) → E (5p+11)`); `reaches_26041` (the first
  eleven rounds from blank tape); the odd sweep `T1` and the top-level ends 2, 3, 5 and the halt at 1, for all
  counts and any tape around them (`lean/Rules.lean`, generated by `lean/rules.py` with
  `tools/py/bbtools/symtm.py`). Axioms: `propext`, `Quot.sound`.
* **Computed:** the complete round map (`py/roundmap.py`), compared with simulation as above; its orbit from blank
  tape for **1,000,000 rounds without a halt**: by then the block has about 205,000 decimal digits (680,000 bits),
  and about 23% of the rounds start with two blocks.
* **Heuristic:** a round halts only when a digit recursion ends exactly: at top level the number left after
  stripping trailing base-6 digits 1 must be 0 (the block is a repunit), in a nested round after digits 5 the
  quotient must come down to 0 in the same way. For a block of `D` base-6 digits both have chance about `6^−D`,
  unless the second block is small, and second blocks are quotients of the first by a small power of 6, so they are
  long too. The chances summed over the rounds beyond the ones already computed are astronomically small: the
  machine very probably never halts, but a proof would have to exclude repunit-like numbers on a `5/2`-type orbit,
  which is a Collatz-like question.

## For later

1. Prove the nested rules in Lean. `symtm` proves each of them directly once the nested phase state is written
   exactly: after the outer even block is rewritten the tape is `L w 0 (01)^k 0 1 … C> 0 1 0 1^x' …` with small
   offsets (`x'` is not `y`; try `python3` with `symtm.run` from `L C> 0 1 0 (11)^k+2 0 (1)^y …`, stopping at the next
   `C> 0 1 0`). Then define the map in Lean (`roundmap.py` is 60 lines), prove one round by induction on the list of
   blocks, and state `HaltsFromBlank ↔ ∃ i, orbit i = halt`.
2. Iterate further (the map costs a few big-number divisions per round) and make the heuristic quantitative.

## Files

- `lean/Rules.lean` (generated by `lean/rules.py`): the symbolic rules of an even round, four concrete runs, the odd
  sweep and the top-level ends.
- `lean/Macro.lean`: `passes`, `even_round`, `reaches_26041`.
- `c/evc.c`: runs the machine from a list of blocks to the next round start.
- `py/rounds.py`: the one-block rule, its check against simulation, and the orbit from blank tape by simulation.
- `py/roundmap.py`: the complete round map on lists of blocks, its check against simulation, and its orbit.

## Status

Open. See above; the claims with what each rests on are in `status.json` and the proof-status page.

## Pages

- [`pages/holdouts/1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC/explainer.html`](../../pages/holdouts/1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC/explainer.html)
- [`pages/holdouts/1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC/proof-status.html`](../../pages/holdouts/1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC/lean/check.sh
python3 holdouts/1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC/lean/rules.py | diff - holdouts/1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC/lean/Rules.lean
python3 holdouts/1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC/py/rounds.py check 2000
python3 holdouts/1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC/py/roundmap.py check 3000 40 4
python3 holdouts/1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC/py/roundmap.py orbit 100000
```
