# 1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF

bbchallenge id 168016, group G12. Whether it halts from blank tape is **open**. Family: a *nested block counter*.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 1RC | 1LB |
| C | 0LD | 0RA |
| D | 1RF | 1LE |
| E | --- | 1LF |
| F | 1LC | 0LF |

## The picture

Whenever the head is in C on the first blank cell right of everything written, the tape is a list of blocks of 1s
separated by single 0s: `[b1, ..., bk]` means `0^inf 1^b1 0 1^b2 0 ... 0 1^bk C>0 0^inf`. A *round* runs from one such
configuration to the next. With A the block in front of the last block n:

* **odd round**: n odd, 3 <= n <= 2A+1: `[.., A, n] -> [.., A, n+2]` in exactly `3*2^((n+3)/2) - 6` steps;
* **even round**: n even, 4 <= n <= 2A+2: `[.., A, n] -> [.., A-1, n-1, 3]` in `6*2^(n/2) - 2n - 2` steps;
* **overflow**: n = 2A+3: the round needs one cell more than A can lend and the recursion below spills into the
  blocks in front.

**The mechanism (new in round 4).** Write `[q, k] C> w` for `L 1^q 0 1^k C>0 w` and `u` for the word `110`. One family
of moves drives everything:

* `M j k` (k odd, q >= (k-1)/2): `[q, k] C> u^j 0 0 R  ->  [q+j, k+2j+2] C> R`, in `3*2^((k+3)/2) - 6 + 2j^2 + (2k+5)j`
  steps; the odd round is `M 0 n`.
* `Z a k` (same conditions): `[q, k] C> u^a 0 u 0 0 R -> [q+a, k+2a+2, 3] C> R`, 4 steps more than `M a k`.
* the **sweep** (k >= 5, `k+6` steps): `[q+1, k] C> w -> [q, 3] C> 0^(k-5) u w`. F erases the block, a marker `11` is
  left at its far end, and the separator in front moves one cell left (one cell is *borrowed* from q).

For k >= 5, `M j k` = sweep, then the odd rounds `M 0 3, M 0 5, ..., M 0 (k-4)` with q-1 (they eat the zeros), then
`M (j+1) (k-2)` with q-1, which swallows the new marker. `Z` recurses the same way. For k = 3 the units `u` are absorbed
one by one by an A/B zigzag (`absorb`: `1^q 0 A> 1^r 0 u X -> 1^(q+1) 0 A> 1^(r+2) 0 X` in 2r+5 steps). So a round of
size n is a recursion of depth (n-3)/2, each level borrowing one cell from the block in front: the binary counter of
`11` markers seen in the space-time diagram is this recursion unrolled. The even round is a sweep, a chain of odd rounds
and `Z 0 (n-3)`.

**Overflow = the recursion running out of cells.** When q < (k-1)/2 the recursion reaches a level with q = 0, where the
sweep's separator meets the separator of the block in front, and the block in front is then swept itself, like a level
up of the same counter. No closed formula for overflows was found (the small-depth rules of `py/overflow.py` are
instances; with deeper lists they change); the overflow *is* this recursion, and `py/accel.py` computes it exactly.

**Halting.** E is entered only from D reading a 1 after C read a 0 and moved left, so the machine halts exactly when C
reads the 0 right of a block of length 1 (`C>0` after `0 1`). In the overflow table above, B = 1 halts.

## The run, computed exactly

`py/accel.py` runs the machine on a run-length tape and applies, besides single steps and shift rules, only the moves
`M`, `Z` and runs of `M 0` proved in `lean/Counter.lean`, with their exact step counts. It reproduces every block
configuration of the 3*10^10-step direct run, agrees with direct simulation on 1,400 random rounds including
overflows (`py/check_accel.py`), and reaches, from blank tape (steps exact in the program output; given here rounded):

| step | blocks | event |
|---|---|---|
| 6,442,649,296 | [4, 42, 66] | overflow from [4, 17, 27, 57] |
| 57,982,256,714 | [4, 41, 65, 3] | even round |
| 8.854e20 | [4, 41, 65, 133] | odd rounds, last block 2A+3 |
| 1.771e21 | [17, 97, 138] | overflow (not the small-block prediction [4, 80, 166]) |
| 5.313e21 | [17, 96, 137, 3] | even round |
| 8.363e42 | [17, 38, 198, 280] | overflow |
| 4.662e85 | [5, 53, 363, 682] | overflow |
| 2.688e103 | [5, 53, 362, 681, 3] | even round |
| 4.816e206 | [20, 35, 123, 227, 710, 1368] | overflow |
| 1.546e413 | [5, 14, 40, 301, 1877, 2992] | overflow |
| 1.153e902 | [20, 35, 77, 151, 697, 1215, 3050, 5988] | overflow |
| 8.868e1803 | [5, 14, 40, 225, 1525, 8815, 12596] | overflow |
| 1.426e3793 | [5, 54, 1609, 3195, 18358, 25196] | overflow |
| > 1e4300 | (run stopped) | no halt so far |

Each epoch is: an even round `[.., Y, n] -> [.., Y-1, n-1, 3]`, odd rounds up to `2(n-1)+3`, and an overflow that takes
about as long as all of that, so the step count roughly squares from epoch to epoch (the exponent doubles). No block of
length 1 is ever swept up to there, so there is **no halt in the first 10^4300 steps** (trusted: the moves are
Lean-proved, the program applying them is checked against direct simulation, not proved).

## What is established

**Proved in Lean, kernel only**: the halting configurations (E reading 0) and no halt in 10,000 steps
(`lean/Blank.lean`); **the odd round law for every odd n >= 3 and every A >= (n-1)/2, and the even round law for every
even n >= 4 and every A >= (n-2)/2, with their exact step counts, by induction on n** (`odd_round`, `even_round`,
`even_round_4`, and the general moves `M_rule`, `Z_rule`, `sweep`, `chain`, `absorb` in `lean/Counter.lean`; axioms
propext and Quot.sound only); the earlier fixed-n rounds (`lean/Rules.lean`); the block configurations at steps 204
and 420 (`lean/Blocks.lean`).

**Proved in Lean with `native_decide`**: no halt in 10^7 steps; `[4,18,28]` at step 99,072 and `[4,17,27,3]` at step
197,318 (`lean/Blocks.lean`).

**Computed** (trusted C/Python): the run above to beyond 10^4300 steps without a halt (about 25 minutes of Python) (`py/accel.py`, checked by
`py/check_accel.py` against `c/blk.c`); the round laws by direct simulation for A <= 22 (`py/verify_rounds.py`); the
small-depth overflow rules (`py/overflow.py`); no halt in 3*10^10 steps by direct simulation (`tools/c/tmrun.c` with
`py/check_run.py`).

**Open**: halting. The run is a counter of unbounded depth; a halt needs some overflow cascade to end with C right of a
block of length 1. The front of the list keeps changing (4, 17, 5, 20, 5, 20, 5, ...: blocks in front are rewritten at
every overflow), so the question is how the deepest levels behave in the long run. Not known; no heuristic argument
for either answer is offered here.

## For later

Turn the accelerated run into a proof of "no halt before step N" in Lean: the moves are proved, so a Lean macro
machine with `M`/`Z`/sweep plus checked single steps (as `tools/lean/TM/Fin.lean` does for plain steps) would make the
10^4300 bound a theorem. Find the invariant of the overflow cascade (what the front blocks can be): the front seems to
alternate between `[5, 14, 40, ...]` / `[20, 35, ...]`-type prefixes, which hints at a counter at the front that could
be described by the same word machine. The q = 0 base cases (`[.., B] 0 0 1^3 C> ...` and `C>0 1 0 u^b`) are the next
rules to prove; with them the overflow becomes a Lean-checked recursion too.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF/lean/check.sh
python3 holdouts/1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF/py/verify_rounds.py 22
python3 holdouts/1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF/py/overflow.py 8 24 9
(cd holdouts/1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF/py && python3 check_accel.py 1000 2 && python3 accel.py 1e400)
gcc -O2 -o tmrun tools/c/tmrun.c
./tmrun 1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF 30000000000 at C R 100000 | python3 holdouts/1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF/py/check_run.py
```

Pages: [`explainer.html`](../../pages/holdouts/1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF/explainer.html),
[`proof-status.html`](../../pages/holdouts/1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF/proof-status.html).
