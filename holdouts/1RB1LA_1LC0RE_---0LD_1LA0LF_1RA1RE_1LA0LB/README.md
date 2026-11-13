# 1RB1LA_1LC0RE_---0LD_1LA0LF_1RA1RE_1LA0LB

bbchallenge id 52677. A BB(6) holdout, group G10 (one side of the tape grows like the square root of the step count, the other more slowly).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LA |
| B | 1LC | 0RE |
| C | --- | 0LD |
| D | 1LA | 0LF |
| E | 1RA | 1RE |
| F | 1LA | 0LB |

Family: **unary blocks split in halves, Collatz-like**. Decision: **open**, now reduced in Lean to an explicit map on
two lists of block lengths. Sibling: `1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LA0LB` (one transition differs; the same analysis, one row of the map differs).

Family: **unary blocks split in halves, Collatz-like**. Decision: **open**, now reduced in Lean to an explicit map on
two lists of block lengths. Sibling: `1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LA0LB` (one transition differs; the same analysis, one row of the map differs).

## What it does

At the moments the head is in state B on a `0` with a block of 1s directly on its left, the tape is always

    ... 0 1^g2 0 1^g1 0 1^k  B> 0  1^b 000 1^b1 000 ...

blocks of 1s separated by one `0` on the left of the head and by `000` on the right. Write `v gs bs` for it, with
the lists `gs = [k, g1, g2, ...]` (nearest first) and `bs = [b, b1, ...]` (b may be 0). The map G from one such
moment to the next (g, b = 0 when absent; `inc j` adds j to the first entry of a list, `inc j [] = [j]`):

| block next to the head | from | to |
|---|---|---|
| none | `v [] bs` | **halt** (B writes 1, C reads 0) |
| k = 1 | `v (1 :: g :: gs) (b :: bs)` | `v ((g + b + 3) :: inc 2 gs) bs` |
| k = 2 | `v (2 :: g :: gs) (b :: bs)` | `v ((b + 2) :: (g + 2) :: inc 1 gs) bs` |
| k = 3 | `v (3 :: gs) bs` | `v gs (0 :: inc 1 bs)` |
| k ≥ 4 | `v (k :: gs) (b :: bs)` | `v ((b + 3) :: (k − 2) :: inc 1 gs) bs` |

Blank tape is at `v [1] []` (`1 B> 0`) after its first step.

**The transfer loop.** With k ≥ 4 and b = 0, the block that moves to the left of the head is `111`, and the row
k = 3 erases it at once: after two rows the block k has lost two 1s and each of its neighbours has gained one, and
the first block on the right is empty again. So a long block next to an empty one is dismantled, half of it going
left and half right, down to 2 ones (k even) or 3 (k odd):

```
1^2 0 1^5 0 1^3 0 1^4 0 1^10 0 1^16 0 111 B> 0             step 1,463: the block 111 is erased
1^2 0 1^5 0 1^3 0 1^4 0 1^10 0 1^16 B> 0 000 1             step 1,467: 16 ones against an empty block
1^2 0 1^5 0 1^3 0 1^4 0 1^11 0 1^14 B> 0 000 1^2           step 1,514: two rules later
1^2 0 1^5 0 1^3 0 1^4 0 1^12 0 1^12 B> 0 000 1^3           step 1,557
...
1^2 0 1^5 0 1^3 0 1^4 0 1^17 0 11 B> 0 000 1^8             step 1,712: 16 = 2 + 2*7, 7 ones went to each side
```

`GA` is G with this loop done in one application.

## Halting

Blocks left of the head are never empty (every row puts blocks ≥ 2 there), so the machine halts in one way only:
the left list is used up, and since only the row k = 3 shortens it without putting something back, every block
left of the head must then be `111`. The typical way: the left list is down to one long block of x ones with an
empty block on the right; the loop turns x = 2j + 5 into a lone block of j + 1, i.e. it halves x + 3, as long as
the numbers stay odd. **If x = 3·(2^m − 1)** (3, 9, 21, 45, 93, ...) the chain ends on a lone `111` and the machine
halts (`bottom_halts`); otherwise an even number turns up and the head goes back to the right.

Counting: the left list is down to a single block about once in 180 applications of GA, with a block of the size
of the tape; a random number of that size is 3·(2^m − 1) with probability about 1/size, which adds up to an
expected number of halts of the order of 0.01 each time the tape doubles, for ever (a heuristic). No residue
invariant is known that excludes a halt.

## What is proved (Lean, kernel unless said otherwise)

- `lean/Rules.lean`: A crosses a block to the left and E to the right, for every length.
- `lean/Map.lean` (by hand):
  - `G_sem`: for every configuration x = `v gs bs`, if `G x = some y` the machine goes from x to y in at least one
    step, and if `G x = none` it halts from x (`v_one`, `v_two`, `v_three`, `v_big`: one theorem per row, for all
    block lengths);
  - **`halts_iff : HaltsFromBlank ↔ ∃ n, orbitFrom (.v [1] []) n = none`**: the machine halts from blank tape if
    and only if the orbit of `v [1] []` under G reaches a configuration with no (or an empty) block left of the head
    (`G_none_iff`). Nothing is assumed;
  - `loop`: the transfer loop for every k, by induction; `GA_sem` and **`halts_iff_fast`**: the same equivalence
    for the accelerated map GA;
  - `bottom_halts`: a lone block of 3·(2^(m+1) − 1) ones with an empty block on its right halts, 2m + 2
    applications of GA later.
- `lean/Orbit.lean`: the orbit under GA does not halt in its first 20,000 applications (kernel) and its first 10^7
  applications (`native_decide`); by the step counts of `c/vsa.c` the latter is 1.9·10^18 steps of the machine.
- `lean/Blank.lean` (generated): the halting configurations; no halt in 10^4 steps (kernel), 10^7 (`native_decide`).

## Computed (trusted, not proved)

- `c/vsa.c` follows GA with exact step counts (128-bit): **no halt in the first 10^9 applications of GA
  (10^16 applications of G), which is 1,508,121,318,047,435,715,005,702 steps of the machine**; the tape then holds 988,764,137 ones.
  Steps grow like the cube of the number of 1s.
- `py/vmap.py check 20000`: the first 20,000 configurations of the orbit under G agree with a direct run of the
  machine cell by cell, at the steps the map says, and the orbit under GA is a subsequence of them.

## Open

Whether the orbit ever uses up the left list. It is a Collatz-like question about the binary digits of the lone
blocks: neither a proof that it never happens nor a halt has been found.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LA_1LC0RE_---0LD_1LA0LF_1RA1RE_1LA0LB/lean/check.sh
cd holdouts/1RB1LA_1LC0RE_---0LD_1LA0LF_1RA1RE_1LA0LB
python3 py/vmap.py check 20000         # the maps against the machine
python3 py/vmap.py run 40              # the orbit under G, with step counts (fast: under GA)
gcc -O2 -o vsa c/vsa.c && ./vsa 1e9 0   # 6 s; 1e12 takes about 100 minutes
```

## Pages

- [`pages/holdouts/1RB1LA_1LC0RE_---0LD_1LA0LF_1RA1RE_1LA0LB/explainer.html`](../../pages/holdouts/1RB1LA_1LC0RE_---0LD_1LA0LF_1RA1RE_1LA0LB/explainer.html)
- [`pages/holdouts/1RB1LA_1LC0RE_---0LD_1LA0LF_1RA1RE_1LA0LB/proof-status.html`](../../pages/holdouts/1RB1LA_1LC0RE_---0LD_1LA0LF_1RA1RE_1LA0LB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LA_1LC0RE_---0LD_1LA0LF_1RA1RE_1LA0LB/lean/check.sh
```
