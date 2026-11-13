# 1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB

bbchallenge id 134427. Halting from blank tape is open; the macro rule moves a quarter of one block into another, a 3/4 map that branches on residues mod 4 (Collatz-like, not yet written exactly).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LC |
| B | 1LC | 0RD |
| C | 0LE | 1LA |
| D | 0RF | 1RA |
| E | 1LA | 0LA |
| F | --- | 0RB |

## What it does

At the moments the head, in A, extends the tape to the right, the tape is two long blocks of 1s with a gap `000`
between them, a few single marks and a tail `0 1`; the right end moves 2 cells each time:

    step 147,381,276   1^1400 000 1^4198 0 1 A>
    step 160,619,690   1^2452 000 1^3148 0 1 A>
    step 168,067,870   1^3239 0 1 000 1^2361 0 1 A>

Most of the time a single 0 **crawls** right through a block of 1s, one cell per 5 steps:

    L 1 1 1 0 C> 1^(n+2) R  ->  L 1^(n+4) 0 1 A> R        (5n+4 steps)

and while a second 0 near the right end steps 3 cells left per crawl, a full round moves about a quarter of
the right block y into the left block: while y ≡ 0, 2 (mod 4), y -> y − ⌈y/4⌉ (4198 -> 3148 -> 2361; 1686 -> 1264
-> 948 -> 711; 2472 -> 1854 -> 1390 -> 1042 -> 781). When y is odd the round ends differently: the left block shrinks
and y grows (2361 -> 5425, 781 -> 2788).

So the macro dynamics is a 3/4-type map with branches on residues mod 4: Collatz-like.

## What is proved

- Lean, kernel (`lean/Rules.lean`, from `py/rules.py`): `crawl`, `a_crawl`.
- Lean (`lean/Blank.lean`, generated): the halting configurations, no halt in 10^4 / 10^7 steps.

## Open

Halting. The round rule above is read off the run (heuristic).

## For later

- Write the round exactly (both residues), as a map on (x, y, marks), check it against all moments of the run, and
  prove its pieces with symtm (the crawl is done).
- Then study the map: does y ever reach a small value in a bad residue?

## Reproduce

```sh
./tokrun 1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB 400000000 a=10,b=1110 R    # the tape at right extensions
python3 holdouts/1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB/py/rules.py > lean/Rules.lean
. /etc/profile.d/lean.sh && holdouts/1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB/lean/check.sh
```

## Pages

- [`pages/holdouts/1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB/explainer.html`](../../pages/holdouts/1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB/explainer.html)
- [`pages/holdouts/1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB/proof-status.html`](../../pages/holdouts/1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB/proof-status.html)
