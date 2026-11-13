# 1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE

bbchallenge id 172044. One of the six-state holdouts whose halting from blank tape is open (group G07).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RD |
| B | 1RC | 1RB |
| C | 1LD | 0RA |
| D | 1RA | 0LE |
| E | 1LF | 0LC |
| F | --- | 1LE |

## What it does

The tape is a list of runs of the words `011`, `110`, `101`, separated by `1^4`, `1^3` or `0`:

    step 1e8: (111011011)^2 (011)^450 (110)^259 1^4 (011)^303 (110)^1011 1^4 (011)^731 (110)^2347 1^4 (011)^2123
              [(110)^11 1^4 (011)^11] x 20 ... (101)^342 1^3 (011)^420 0 (101)^175 1^3 (011)^634 (110)^479 1 (010)^905 01

The left part (through the twenty equal blocks) is unchanged at step 2e8; the activity is at the right end, where
the list grows. The halting transition is F0, reached only as `0 0 D>1` (D1 -> 0LE, E0 -> 1LF).

**A list of counters, read with `c/tok.c`.** Seen as run-length tokens (`011^c` is the word 011 repeated c times),
at every visit of the right end in state A the tape is a list of counters `011^c` separated by `0 1^4` or `0101 1`,
ending in a growing block `110^m` or a fresh counter. Over 2.8·10^7 visits (10^15 steps) the list keeps about 50-77
tokens; the counters at the right end are worked on, one shrinking at a steady rate while the block at the end grows
(about 1,500 per 10^6 visits each), and the ones at the left change more and more rarely. Samples of the last
counters:

    visits 1e6    step 1.06e12   ... 011^36147 . 011^312866 . 011^217864 . 011^185970 0 1 0 110^126391
    visits 1e7    step 1.06e14   ... 011^880368 . 011^2866633 . 011^204281 . 011^3172504 0 1 0 110^871891
    visits 2.8e7  step 9.73e14   ... 011^2482146 . 011^1085286 . 011^4382435 . 011^13188604 0 1 0 110^495835

and the first ones (011^410, 011^255, 011^213, ... at 10^6 visits; 011^352, 011^256, ... at 2.8·10^7) barely move.
So this is a counter machine whose active counters sit at the right end and whose old counters are left behind,
like 1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF.

## Status

Open.

- **Kernel / native:** `lean/Blank.lean` (halting configurations; no halt in 10^4 steps by the kernel, 10^7 by
  `native_decide`).
- **Trusted computation:** `c/tok.c`, an exact run-length simulator (it agrees with `tools/c/tmrun.c` on the number
  of 1s at step 10,000,087,134), runs 10^15 steps without a halt.
- **Open:** the transfer rule of the active counters. The halting transition F0 (reached as D1 -> 0LE, E0 -> 1LF);
  a closed tape language from windows of 4 cells leaves halts possible inside the tape, not only at an edge.

## Next steps

Write the per-visit change of the last three counters exactly (one counter loses, the end block gains; find the
period and prove it with `bbtools.symtm` for symbolic counters), then the event when a counter runs out, and
iterate the resulting counter machine.

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE/lean/check.sh
gcc -O2 -o tok holdouts/1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE/c/tok.c
./tok 1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE 1e15 A R 1000000     # the tape every 10^6 visits, ~4 min
```

## Pages

- [`pages/holdouts/1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE/explainer.html`](../../pages/holdouts/1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE/explainer.html)
- [`pages/holdouts/1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE/proof-status.html`](../../pages/holdouts/1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0LC_1LC0RE_1LD1LB_1LA1LD_1RF0RA_---1RE`](../1RB0LC_1LC0RE_1LD1LB_1LA1LD_1RF0RA_---1RE/README.md): rename A→C, B→D, C→A, D→B, E→E, F→F and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
