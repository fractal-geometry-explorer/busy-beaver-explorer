# The base-5 family read as digit strings (technique D of the second brainstorm)

27 November 2026. This is the half-day look that [`technique-brainstorm-2-nov27.md`](../technique-brainstorm-2-nov27.md)
proposes as technique D for the base-5 family (R01, the forty machines on the core
`1RB0LC_0RC0RB_1LD0RE_0LE?LF_1LA0LB_??---`; shared analysis in
[`holdouts/1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---`](../../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---/README.md)).

**Outcome: no invariant and no bound. Nothing is decided.** The digit strings are far from random, and the look
explains where they come from, but the regular invariant the brainstorm hoped for ("some digit in the top third of a
drift differs from 0 and from 4") is false: three drifts were found in which more than a hundred leading digits
cancel exactly. Congruences on the low digits fail too. The technique is parked for this family.

Everything below is observed on exact runs of `py/fast.py` (trusted, not proved) unless a Lean theorem is named.
Tools and data: [`../tools/digit-strings/`](../tools/digit-strings/).

## What was run

| run | size |
|---|---|
| `1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---`, every left-end block list | 10^400 steps, 994 left-end events, 285 blocks at the end |
| the 37 list machines of the family, cancelled digits of every new drift (`survey_1e200.json`) | 10^200 steps each, 19,069 events, 43,514 new drifts |
| `1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE---` and `1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RB---`, to the deep small drifts recorded in `data/f05_timing.json` (`coincidences.json`) | 10^611 and 10^695 steps |
| the end of the list on its own, behind blocks that cannot run out (`pure.py`) | 400 left-end events from seven starting lists |

No run halted.

## Where the digits come from

Notation as in the family README: at a left-end event the list is `[6, t_0, t_1, ..., t_k]`, and the drift of two
neighbours is `d_j = t_(j+1) - 5 t_j`.

1. **Rates.** One left-end round lowers block j by `18·5^j` and raises the last block by `12·5^k` (`go_closed`,
   `sweep`, Lean). Measured in rounds, every block but the last is a clock `t_j / (18·5^j)` that counts down at speed
   one, and the last block counts up at speed 2/3. A block that runs out is removed, and every block after it
   moves down one or two places, which multiplies its clock by 5 or 25.
2. **The factor 2/3.** While a block of size t runs out, the last block gains `(2/3)·5^m·t`. Dividing by 3 in base 5
   gives periodic digits. This is what the strings show: beside runs of 0 and of 4, the blocks at the end of the list
   have periods 2 (`1313...`, thirds), 6 (`210234...`, ninths), 18 (`112200430332244014...`, 27ths) and 54. For
   example `1.(13)` is 4/3, `2.(102342)` is 20/9 and `1.0(112200430332244014)` is 142/135.
3. **Merges add drifts.** Between merges the drifts are conserved (`visit_conserves`, Lean). At a merge the new
   drifts are sums of two old ones plus a small constant. Two kinds occur: block j is removed and the drifts on its
   two sides add (`d_(j-1) + d_j + c`), or block j is removed and its two neighbours join into one block, so that four
   drifts become two (`d_(j-2) + d_j + c`, `d_(j-1) + d_(j+1) + c'`). In the 10^400 run, 413 new drifts are such sums
   (258 of neighbours, 151 of next-but-one neighbours, 4 others), with c between -56 and 18. The other 1,488 new
   drifts are not sums of old ones, and 1,471 of them appear within the last four places of the list.
4. **Two kinds of string.** Away from the end of the list almost every block is a string with no visible pattern
   (11,905 of 12,029 sampled blocks beyond place 40). These strings are shared: neighbours carry the same string
   shifted by one digit, which is drift conservation seen in digits, and 11% of the sampled drifts are periodic for
   that reason. Patterned blocks live only at the end of the list.
5. **The end of the list makes the patternless strings itself.** Behind a prefix that cannot run out, the end of the
   list either falls into a cycle of four rounds (new block `2144...441`; then `1134...4412 | 400...044`; then
   `3044...4412 | 13334210234... | 2102342...`; then all of it joins the last prefix block), or it grows a new list
   of about a hundred blocks in 400 rounds whose strings have no pattern (the cycle from two of seven starting
   lists, which are neighbouring events of one run; the new list from the other five). So the
   irregular strings are not inherited from the early run. They are produced again and again by repeated
   multiplication by 2/3 with rounding, and that is a Collatz-like map written in base 5.

## The proposed invariant is false

For every new drift (after event 40, at place 12 or deeper) count the leading base-5 digits that cancel: the digits of
the larger of `5 t_j` and `t_(j+1)` minus the digits of `d_j`.

| digits cancelled | 0 | 1 | 2 | 3 | 4 | 5 to 29 | 30 | 102 |
|---|---|---|---|---|---|---|---|---|
| new drifts (37 machines, 10^200 steps) | 30,553 | 11,741 | 1,003 | 184 | 28 | 0 | 1 | 4 |

The left part is what unrelated numbers would give (after the first, each further digit costs a factor of 5 to 12). The right part is
not chance. The four cases with 102 digits are one event shared by four machines whose runs agree there. The long
runs give three such events in all:

| machine | left-end event | digits of the step count | place j | base-5 digits of block j | drift |
|---|---|---|---|---|---|
| `1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE---` | 409 | 159 | 110 | 113 | -82,025,892 |
| `1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE---` | 1,522 | 612 | 434 | 437 | -82,025,892 |
| `1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RB---` | 1,817 | 696 | 495 | 497 | -6,003,356,234 |

In each of them two neighbouring blocks at the end of the list have the same periodic string, one digit apart:

    t_110 = 1011220043033224401411220043...0343412024120      (113 digits)
    t_111 = 1011220043033224401411220043...03302120424113     (114 digits)

The periodic parts cancel in `t_111 - 5 t_110`, and what is left is the difference of the last twelve digits. The
first two rows are the same event 324 places apart: the last five blocks before the round and the last six after it have
the same thirty leading and thirty trailing digits at both depths, and the drift is the same number. So a drift of this kind is a constant
of the pattern at the end of the list, not of the depth.

This is the opposite of the invariant hoped for. It also corrects the sentence in the family README that the
drifts "behave like differences of unrelated large numbers": most do, and a few are exact coincidences.

The low digits give no obstruction either. Of 2,426 new drifts in the 10^400 run, the number that agree with a value
of the halting window modulo 5^e is what chance predicts for e up to 5 and above it for e = 6, 7, 8 (4, 3 and 2
drifts where fewer than one is expected), because patterned numbers end in runs of 0 and 4. Residues modulo 2, 3,
4, 9, 18, 36 and 90, alone and together with `t_j mod 18`, exclude nothing beyond "every drift is even".

## What this says about the halt

A halt needs a new drift inside a window of about -24 to 8 (family README, `data/f05_danger.json`). A conserved drift
never changes, so only new drifts matter, and they come in two kinds.

- **Drifts between patternless blocks** (sums at merges, and most drifts born at the end). Their leading digits
  cancel like those of unrelated numbers. At place j a halt needs about j digits to cancel, and new drifts are made
  deeper and deeper. This is the old heuristic argument, with better data, and it proves nothing.
- **Exact coincidences between patterned blocks.** These do bring a drift from hundreds of digits down to ten. What
  is left is the difference of the short non-periodic ends of two patterned numbers. The three seen are 12 to 14
  base-5 digits long. A halt would need a pattern whose remainder is in the window. Nothing found bounds the
  remainder from below, and the set of patterns is not finite, because the end of the list is itself the
  Collatz-like map of point 5.

Neither kind gives a statement that could be proved by a finite check, so the question stays where it was.

## What was not done

- The three machines that need the raw simulator (`hybrid2.py`) and the machines of R01 outside the forty are not in
  the survey.
- The other targets named for technique D (the four odometers, R04 in base 4, R11 in base 3) were not looked at.
- The rules of points 1 to 3 are read off the runs and the proved rules. They were not written as a model and
  checked against the machine. A model of the list as clocks (point 1) with the two merge kinds and the birth rule
  would reproduce the patterned numbers exactly, and it would turn "which coincidences can occur, and with which
  remainders" into a computation on the end of the list alone. That is several days of work, and the most it could
  give is a better estimate of how unlikely a halt is.

## Reproduce

```sh
cd holdouts/recent-proofs/tools/digit-strings
python3 dump.py 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA--- 1e400 ev.jsonl      # every left-end list (2 minutes)
python3 canc.py 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE--- 1e200 out.json 5    # cancelled digits of new drifts (1 minute per machine)
python3 small.py 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RE--- 1e640 hits.jsonl   # the two coincidences of that machine (20 minutes)
python3 pure.py 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA--- 300 60 400 out.json # the end of the list alone: the four-round cycle
python3 pure.py 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA--- 200 40 400 out.json # the same from another list: a new patternless list
```

`b5.py` prints numbers in base 5. `survey_1e200.json` holds the histogram for each of the 37 machines and
`coincidences.json` the last seven blocks before and after each of the three events, in base 5.
