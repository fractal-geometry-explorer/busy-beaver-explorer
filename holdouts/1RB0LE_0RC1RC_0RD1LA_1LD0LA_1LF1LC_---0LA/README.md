# 1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA

bbchallenge id 133227. Group G01. **Two counters** (structure found, map not yet): (10)^a 1^b [0] C> 0, with b following an irregular growth map while a pays. Open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LE |
| B | 0RC | 1RC |
| C | 0RD | 1LA |
| D | 1LD | 0LA |
| E | 1LF | 1LC |
| F | --- | 0LA |

## What it does

At the moments when the head is in state C at the right end on a 0:

    X(a, b) = 0^inf (10)^a 1^b C> 0^inf        Y(a, b) = 0^inf (10)^a 1^b 0 C> 0^inf

For a large enough, X(a, b) → X(a − d(b), f(b)) for even b and → Y(a − d(b), f(b)) for odd b, with f, d
independent of a (b = 0..13: f = 10, 8, 22, 32, 16, 44, 46, 38, 58, 38, 52, 50, 70, 44; d = 4, 3, 8, 13, 4, 17,
18, 13, 22, 13, 18, 17, 26, 13); Y(a, b) does the same with f larger by 2 to 4 and the kinds swapped.
Steps are linear in a. f(b) ≈ 3.5b, irregular (a period-3 pattern in b/2 plus jumps).

Run from blank tape: Y(84, 7) → X(71, 40) → X(33, 124) → …, Y(322, 7) → X(309, 40) → X(271, 124) → X(127, 424) →
X(318, 369) (step 1,168,114): when a cannot pay, the 1s are turned back into `10`s. At step 1.5·10⁸:
(10)^784 1^8773.

## One function pair for both kinds (second pass)

From Y(a, b) the next event is exactly **Y(a − d(b) − 2, f(b) + 4)** for even b and **X(a − d(b), f(b) + 2)** for
odd b, where (f, d) is the X-table; X results do not depend on a (two values tried). Checked for every b < 400
(`py/bmap.py 400`, under a second, mirror image run by `c/evrun2.c` of 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---).
For even b, f changes by +12, −6 as the last ternary digit of b/2 steps 0 → 1 → 2, and the carries add amounts that
depend on the higher digits: f looks 3-regular (a finite automaton on the ternary digits), the likely route to a
closed form.

## What is proved

| level | result | where |
|---|---|---|
| kernel | halting configurations; no halt in 10⁴ steps (10⁷ by native_decide) | `lean/Blank.lean` |
| trusted | no halt in 10⁹ steps | `holdouts/triage.json` |
| trusted | the b-map table above (b < 70) | `py/explore.py 400 70` |
| open | f, d in closed form; the turnover; halting | |
| trusted | the b-map for b < 400 and the exact X/Y relation | `py/bmap.py 400` |

## Further work

Decompose one round (the 1^b block is processed in passes, probably in base 3) to get f and d in closed form;
map the turnover when a is too small; then the halting condition (some synthetic starts halt).

## Third pass

The macro simulator `c/msim.c` (a copy of the one in holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---, in
`c/`; blocks of 6 cells; checked against the direct simulator at 10⁹ steps by `check_msim.py check`) runs
10¹⁸ steps from blank tape without a halt: `python3 py/check_msim.py run 1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA 1e18` (2 to 5 minutes).
At the end the tape is `(10)^212071119 101 (011)^71857433 1^30536790 …`: still the two counters.

Inside a round two zig-zag loops do the work (seen in `py/explore.py` traces; the first is a theorem that
`bbtools.symtm.prove` writes, 10j + 17 steps a turn):

    α:  1^k 0 D> (101)^(j+1) 1 00 1^m   →   1^(k+1) 0 D> (101)^j 1 00 1^(m+2)        (a (101) becomes three 1s)
    β:  (10)^A 11 B> 0101 (101)^i 1^m   →   (10)^(A−2) 11 B> 0101 (101)^(i+2) 1^(m−2)  (two (10)s pay for two (101)s)

so a round is a chain of conversions 1^m → (101)^(m/2) → 1^(…) with the leftovers decided by parities and by
remainders mod 3, which is where the base-3 pattern of f comes from. f in closed form is still open.

No pushdown certificate with a small DFA exists: the reduction of `bb6-1RB0LF_1RC0LB/c/pds.c` (one side of the tape
exact, the other a DFA, post* saturation) reaches a halt for every DFA with at most 6 states, on either side
(`TM=1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA ./pds 6 L`, then `R`; 1.5 minutes each).

## Pages

- [`pages/holdouts/1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/explainer.html`](../../pages/holdouts/1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/explainer.html)
- [`pages/holdouts/1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/proof-status.html`](../../pages/holdouts/1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/proof-status.html)
