# 1RB0LA_0RC1RD_0LD1RE_1LA0RF_0RD0LD_1RD---

bbchallenge id 10681. Group G01. **A Collatz-like map on a list of blocks**, analysis only begun. Open.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LA |
| B | 0RC | 1RD |
| C | 0LD | 1RE |
| D | 1LA | 0RF |
| E | 0RD | 0LD |
| F | 1RD | --- |

## What it does

Sample the run when the head is in state A at the left end, reading `00 1`. The tape is then a list of blocks:

    X(n)    = A> 00 (10)^n 01
    Y(a, b) = A> 00 1010 (010)^a (10)^b 01            (Y(0, b) = X(b + 2))

and longer lists such as `A> 00 (10)^1529 (010)^1529 00 (10)^4585 (01)^2 00 1`. Two rules are clear:

    X(n), n even   ->  Y(n/2 - 1, 3n/2)
    Y(a, b), a odd ->  X(b + (3a + 11)/2)

so X(n) with n ≡ 0 (mod 4) goes to X((9n + 16)/4). From blank tape: X(400) at step 227,603, Y(199, 600), X(904),
Y(451, 1356), X(2038), Y(1018, 3057), then longer lists. At step 1.36·10¹⁰ the tape is
`A> 00 (10)^863 (010)^19422 00 (10)^58264 (01)^2 00 1`.

X(n) with n odd and Y(a, b) with a even start longer block lists, and so far these have always come back to an X or
Y form. Their rules are not yet written down, so neither the halting condition nor a heuristic is available yet.

Between two such events the tape passes through `A> (10)^2 …`, `A> 0^3 …` and `A> 1^2 …` at the left end within a
few steps; those are not used.

## New rules (second pass)

With X(n) = `A> 00 (10)^n 01`, Y(a, b) = `A> 00 1010 (010)^a (10)^b 01` and
Z(a, b) = `A> 00 1010 (010)^a 00 (10)^b (01)^2 00 1` (head at the left end in state A, tape starting `001`):

| from | next event |
|---|---|
| X(2k) | Y(k − 1, 3k) |
| Y(2i+1, b) | X(b + 3i + 7) |
| X(2k+1) | Z(k, 3k − 2) |
| Z(2i+1, b) | `A> 00 (10)^(3i+5) 00 (10)^(b−1) (01)^5 00 1` |
| Z(2i, 2j) | `A> 00 (10)^(3i+4) (010)^j 00 (10)^(3j+1) (01)^2 00 1` |
| Z(2i, 2j+1) | `A> 00 (10)^(3i+4) (010)^j (10)^(3j+6) 01` |

All checked by direct simulation for every parameter below 40 (3,060 cases, `py/listrules.py 40`). The pattern:
the leftmost segment `(10)^x (010)^y` is rewritten by a 3/2-type rule and its parity decides whether the next
segment is merged into it or a separator `00` stays and the list grows. With a leftmost `(10)^x`, x ≠ 2, the
outcomes are more varied (`(00101)^2 …`, `(0010100)^2 …`); those are the next thing to map.

**Twin.** Mirroring and renaming the states (A→B, B→C, C→D, D→A) gives `1RB0LF_1LC0RB_0LD1LA_0RA1LE_0LA0RA_1LA---` (group G02): the same
machine started in another state; these rules hold there in mirror image.

## What is proved

| level | result | where |
|---|---|---|
| kernel | the halting configurations (F1); no halt in 10⁴ steps | `lean/Blank.lean` (generated) |
| native | no halt in 10⁷ steps | `lean/Blank.lean` |
| trusted | the two rules above hold at every blank-run event where they apply, up to 1.4·10¹⁰ steps (7 cases) | `py/events.py blank 1.4e10` |
| trusted | X(2k+1) → Z, and three Z rules (3,060 cases with the two earlier rules) | `py/listrules.py 40` |

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LA_0RC1RD_0LD1RE_1LA0RF_0RD0LD_1RD---/lean/check.sh
python3 holdouts/1RB0LA_0RC1RD_0LD1RE_1LA0RF_0RD0LD_1RD---/py/events.py blank 1.4e10    # 2 min
```

## Further work

More than a day. The next steps:

- Write the general block-list form and its rules: how X(n odd) and Y(a even, b) unfold, which lists appear, and how
  they collapse. The samples suggest each level runs a 3/2 map whose parity decides whether a new block is pushed.
- Find the halting configurations (F1 read) of the block-list map, iterate it, and give a heuristic.
- Compare with `1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---`, which also has `(100)`/`(010)` blocks and a single-number
  regime with parity-triggered nesting.

## Third pass

**Gap form.** On this tape no two 1s are adjacent, so an event is a word of gaps (the number of 0s between
consecutive 1s), run-length coded: X(n) = `1^(n−1) 2`, Y(a, b) = `1 2^a 1^b 2`. The events from blank tape
(direct simulation, 9.5·10¹⁰ steps) in this form:

    1^399 2 → 1 2^199 1^600 2 → 1^903 2 → 1 2^451 1^1356 2 → 1^2037 2 → 1 2^1018 1^3057 2
    → 1^1528 2^1529 3 1^4584 2 1 2 → 1 2^764 3 1^3055 2^1911 1^8028 2 → 1^1149 2^1528 3 1^15476 2 1 2
    → 1 2^574 1^38843 2 → 1^862 2^19422 3 1^58263 2 1 2 → 1 2^431 3 1^73260 2^43484 1^131745 2

Each event is a short list of runs of gaps 1 and 2 with single 3s as separators; a pass halves a run of 1s into 2s
and multiplies what it pushes on by 3/2 (1018 → 1527, 3057 → 1529 and 4584), and an odd run leaves a 3. This is the
list the six rules of the second pass describe piecewise; the general rule on gap lists is the next step.

The macro simulator `c/msim.c` (a copy of the one in holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---, in
`../1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/c/`; blocks of 6 cells; checked against the direct simulator at 10⁹ steps by `check_msim.py check`) runs
10¹⁸ steps from blank tape without a halt: `python3 ../1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/py/check_msim.py run 1RB0LA_0RC1RD_0LD1RE_1LA0RF_0RD0LD_1RD--- 1e18` (2 to 5 minutes).
(The community tracker has it as "a Bell with several counters, growing by about 3/2 or by irregular doubling",
simulated to 3.5·10⁷⁹ with its rules.)

No pushdown certificate with a small DFA exists: the reduction of `bb6-1RB0LF_1RC0LB/c/pds.c` (one side of the tape
exact, the other a DFA, post* saturation) reaches a halt for every DFA with at most 6 states, on either side
(`TM=1RB0LA_0RC1RD_0LD1RE_1LA0RF_0RD0LD_1RD--- ./pds 6 L`, then `R`; 1.5 minutes each).

## Pages

- [`pages/holdouts/1RB0LA_0RC1RD_0LD1RE_1LA0RF_0RD0LD_1RD---/explainer.html`](../../pages/holdouts/1RB0LA_0RC1RD_0LD1RE_1LA0RF_0RD0LD_1RD---/explainer.html)
- [`pages/holdouts/1RB0LA_0RC1RD_0LD1RE_1LA0RF_0RD0LD_1RD---/proof-status.html`](../../pages/holdouts/1RB0LA_0RC1RD_0LD1RE_1LA0RF_0RD0LD_1RD---/proof-status.html)
