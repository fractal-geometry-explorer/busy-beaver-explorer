# 1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF

bbchallenge id 71111. One of the six-state holdouts whose halting from blank tape is open (group G07).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RD |
| B | 1LC | 0RD |
| C | 0LE | 1RD |
| D | 1RA | 0RB |
| E | --- | 1LF |
| F | 1RA | 0LF |

## What it does

Most of the tape is the word `00000101000` repeated; at the left end the tape repeats every 80 visits (in two alternating forms near step 3·10^8, so 160) of the
left end (state F), the bulk gaining 7 words. The other 3 cells per period go to a list of counters at the right:

    step 94,467,133:  ... (00000101000)^1897 0101 0^4 (101)^21 00101 0^4 (101)^11 0^4 (101)^17 00101 0^4 (101)^90 00101 0^4 (101)^12 00 (101)^92 ...
    step 95,160,717:  ... (00000101000)^1904 0101 0^4 (101)^18 00101 0^4 (101)^14 0^4 (101)^17 00101 0^4 (101)^90 00101 0^4 (101)^13 00 (101)^92 ...

**The counter list.** Sampled every 160 visits of the left end (state F), the bulk `(00000101000)^n` gains 7 words
and the list right of it is a list of counters, the lengths of the runs `(101)^c` (separated by `00101 0^4`, `00`
and similar short words). Inside a stretch the first counter loses 3 while the next two gain 2 each on average,
e.g. (step 3.81·10^8 to 4.0·10^8):

    (123, 134, 113, 88, 5, 2) -> (120, 135, 116, 88, 5, 2) -> (117, 138, 117, 88, 5, 2) -> ... -> (80, 161, 140, 88, 5, 2)

and when the first counter runs out the list is reorganised: new small counters appear at the front and the
mass moves right. The last large counter grows (to 1,553 at step 3.96·10^9: list (52, 2, 2, 52, 1553, 2)), the deep
ones change rarely: a multi-counter machine with transfers, like a Collatz-type counter system. Samples
(steps, bulk words, counters):

    2.1e7   928   (83, 5, 2, 33, 2)
    3.3e8   3592  (223, 66, 44, 88, 5, 2)
    1.03e9  6298  (245, 246, 82, 237, 2)
    2.04e9  8853  (291, 78, 805, 2)
    3.0e9   10743 (211, 72, 1158, 2)
    3.96e9  12356 (52, 2, 2, 52, 1553, 2)

The halting transition is E0, reached only as `0 0 B>0` (B0 -> 1LC, C0 -> 0LE, E0 halts).

## Status

Open. Lean: `lean/Blank.lean`. C: no halt in 1e9 steps.

## Next steps

Write the transfer rule of the first counters exactly (prove the 160-visit step with `bbtools.symtm` for a symbolic
first counter), then the reorganisation when it runs out, and simulate the resulting counter machine far beyond
direct simulation.

## Pages

- [`pages/holdouts/1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF/explainer.html`](../../pages/holdouts/1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF/explainer.html)
- [`pages/holdouts/1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF/proof-status.html`](../../pages/holdouts/1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF/lean/check.sh
```
