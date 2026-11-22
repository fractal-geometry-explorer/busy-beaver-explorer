# 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD

bbchallenge id 126068. A bouncer at the left end grows two blocks at fixed rates ((011) by 1 and (01) by 3 per two left visits) for an ever longer epoch; then a long pass empties them into an irregular region on the right, which grows from epoch to epoch.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LC |
| B | 1RC | 1RA |
| C | 1RD | 0RF |
| D | 0LE | --- |
| E | 1LA | 1LE |
| F | 0RA | 1LD |

## What it does

The run is a sequence of **epochs**. At the head's visits to the left end (state C) the tape starts

    step 403,575,993:  C>0 (011)^1131 (101)^3 (01)^221 (101)^3 0 …
    step 414,251,793:  C>0 (011)^1331 (101)^3 (01)^821 (101)^3 0 …       (400 visits later)
    …
    step 857,064,593:  C>0 (011)^4531 (101)^3 (01)^10421 (101)^3 0 …

Within an epoch every 400 visits add 200 to the `(011)` block and 600 to the `(01)` block, and the rest of the
tape, an **irregular region** of short blocks and walls on the right, does not change (1,581 compressed words).
An epoch ends with a long pass that empties the two blocks into the irregular region; then a new epoch starts
with small blocks and a larger region (5,017 words after the epoch that ends between 8.6·10⁸ and 1.7·10⁹ steps). Epochs grow
longer: they end between 1.1 and 1.6·10⁸, between 3.1 and 4.0·10⁸ and between 8.6·10⁸ and 1.7·10⁹ steps, and none ends
between 1.7·10⁹ and 2·10⁹.

So the left side, where the blocks grow, grows like √t, and the right side, which grows only at epoch ends, grows
like t^0.31.

## What is proved

- Lean, kernel only (`lean/Blank.lean`, generated): the halting configurations (`step_none_iff`) and no halt in the first 10,000 steps; with `native_decide`, none in the first 10<sup>7</sup>.
- Lean, kernel only (`lean/Pulse.lean`): one pulse over any list of words takes three 1s from the run after them and leaves the words as they were (`pulse`); a pulse that meets `0001` halts (`pulse_halt`). See The pulse in Lean.
- Lean, kernel only (`lean/Rules.lean`, written by `py/rules.py`): the shift rules: A crosses `(100)^n` leftward (into `(110)^n`) and `(01)^n` rightward (into `(11)^n`) (`shift_l_A_100`, `shift_r_A_01`).
- C (`tools/c/triage.c`, trusted): no halt in the first 10<sup>9</sup> steps.

Everything else above is measured on runs (heuristic), not proved.

## Open

Whether it halts. Observed: it halts exactly if a pulse ever meets an inner `000` (see Pulses and defects). The
fuses are understood; the `00` pulses, which end the epochs and build the irregular region, are not.

## For later

More than a day. Next: (1) prove the one-visit rule inside an epoch (a, b) → (a, b) + (1/2, 3/2) per visit
(two visits per cycle) with `symtm.prove`; (2) find the condition that ends an epoch (a and b at the end:
(1867, 5602), (4531, 10421)); (3) follow one dump in detail and see whether the irregular region is a list of
counts processed by a fixed rule.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD/lean/check.sh
python3 holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD/py/rules.py          # rewrites lean/Rules.lean
python3 holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD/py/observe.py 1e7 B 6  # the tape at the last moments each end grew
```

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 14, history 1 up to width 13, history 2 up to width 12, history 3 up to width 12, LRU history up to width 5 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 12, p = 3 up to width 12, p = 4 up to width 12, p = 6 up to width 12.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..9; n = 10 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: B with 0 under the head, 0 right, 1 two right.

## Pages

- [`pages/holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD/explainer.html`](../../pages/holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD/explainer.html)
- [`pages/holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD/proof-status.html`](../../pages/holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD/proof-status.html)

## Start B of a PR 93 neighbour table (22 November 2026)

This machine is the table of 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE started in state B, mirrored (see Related machines). With E and F of that machine
exchanged and its halting detour replaced by one step, the table is `1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB1RF_0RA---`, which is DeepMind's busycoq PR 93 table T4
with one transition (E1) changed. Of PR 93's 18 basic macro rules, 14 still hold; the four that pass through E1 change:
this table turns right at the E1 step and runs on into the tape beyond the rule, where PR 93's rules return to the left. So PR 93's engine does not carry over to this table, from any start. Details, and Lean proofs of
the changed rules, are in [1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE](../1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/README.md#pr-93s-engine-on-this-table-22-november-2026).

Run for a halt from this start: the accelerated simulator `rsim.py`, validated against direct simulation at 5 points up to 3·10^9 steps,
went 6,232,238,054 steps from blank tape in 20 minutes without a halt (199 jumps).

```sh
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD 1200
```

## Lead 20 rechecked, longer runs and the fuse (22 November 2026)

- **PR 93's engine, rechecked.** In the renamed table G = `1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB1RF_0RA---` (section above), PR 93's
  collision rule `CfgL (001101 l) r → CfgJ l (1111 r)` was simulated again from scratch with 30 random cells on each
  side: for T4 it ends in its rule form (`CfgL l (111111 r)`, 10 steps) in 40 of 40 cases; for G the head runs more
  than 7 cells into `r` in 29 of 40, and in the other 11 it comes back to `l` in B with a different tape, never the
  rule form. This agrees with PR #410, so the engine
  does not carry over and this lead is closed. An engine for this machine has to be built from its own passes (below).
- **Direct run.** `tools/c/tmrun.c` runs 10^12 steps from blank tape without a halt; the tape then holds 1,071,316
  ones (about an hour).
- **Accelerated run.** The C++ port `rsim_fast` (in the folder of 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF) runs
  19,424,261,661,128 steps (1.9·10^13) in one hour without a halt (7,491 tape-level jumps, validated, not proved).
- **The passes of an epoch (observed).** `c/passes.c` prints, for each return of the head to the left end, how far
  right it got. Inside an epoch the returns alternate between a short pass, which turns at the end of the
  `(011)^a` block, and a long pass, which crosses the `(01)^b` block and the irregular region and turns at the
  left end of a run of 1s near the right end of the tape. Each long pass shortens that run by 3 cells, so the run
  is a **fuse**: for example `1^29` at step 179,100 is used up 3 at a time until step 209,010, and the next long
  pass runs to the right end of the tape. That is the end of the epoch; the same alternation is seen in the epoch
  at 4·10^8 steps (short passes turning about 3,180 cells from the left end, long ones about 9,290, on a run of 1s).
  So the length of an epoch is set by the fuse the previous dump left behind.
- **Long stretches away from the left end.** The stretches of more than 10^6 steps in which the head reaches the
  right end of the tape before coming back end at steps 1.2·10^7, 3.2·10^7, 4.7·10^7, 5.8·10^7, 8.5·10^7,
  1.6·10^8, 4.0·10^8, 1.45·10^9, 4.03·10^9 and then in clusters near 1.1–1.5·10^10, 1.7·10^10, 3.0·10^10 and
  3.7·10^10; the longest take 5.8·10^8, 1.4·10^9, 1.3·10^9 and 9.6·10^9 steps. None between 3.73·10^10 and
  3·10^11 steps (`passes 0 300000000000 ends`, the same run, no halt in 3·10^11 steps).

```sh
gcc -O2 -o passes holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD/c/passes.c
./passes 179000 210000 | cut -c1-140          # short and long passes, the fuse 1^29 eaten 3 cells at a time
./passes 0 300000000000 ends                  # the long stretches that reach the right end (about 20 minutes)
```

## Pulses and defects: what an epoch end is (22 November 2026)

Observed and tested on random tapes, not proved. `py/pulses.py` and `c/defects.c` reproduce everything here.

- **Transparent words.** Look at the tape at a return of the head to the left end in the form
  `C>0 (011)^a 001101 …`. After `001101` it is mostly made of *words*: a run of one or two 1s followed by a single 0.
  Runs of one or two 1s with single 0s between them are transparent: a round trip of the head (two returns to the
  left end) leaves any such stretch exactly as it was. Replacing the 307 cells of words at step 182,483 by 30 random
  lists of words `10`/`110` of other lengths changes nothing else: in every case the round trip only adds 1 to a,
  three words at the left, and takes 3 from the run of 1s after the words.
- **Defects and pulses.** Where the tape is not made of words there is a *defect*: a run of k ≥ 3 ones, or a run of
  two or more 0s. A round trip goes right in state A (rules `A> 01 → 11 A>` and `A> 011 → 100 A>`, which hold for
  every tape on the left), meets the first defect and comes back. So each round trip sends one **pulse** to the
  first defect and only that defect changes. Tested with 20 random word lists around each defect:

  | first defect | after one pulse |
  |---|---|
  | `1^k`, k ≥ 6 | `1^(k−3)` (this is the fuse of the section above) |
  | `1^4`, `1^5` | dissolves into a word (`1`, `11`) |
  | `1^3` | becomes `00` |
  | `000` with tape after it | **the machine halts** (20 of 20, and with other tapes after it) |
  | `00` | a zigzag around the `00`; the result depends on the words themselves, not only on how many there are, and it often rewrites the left part (a starts again from 1 or 2) |

  So a fuse `1^k` lasts ⌊k/3⌋ pulses and then leaves nothing (k ≡ 1, 2 mod 3) or a `00` (k ≡ 0 mod 3).
- **Epoch ends are `00` pulses.** On the run from blank tape, of the 9,714 round trips that start in the form above
  in the first 3·10^10 steps, all but 1,766 follow the table's first three rows. Of the 1,766, 1,755 start with a
  `00` as first defect and 7 with no defect at all (the pulse goes to the end of the tape); the other 4 are a `1^3`
  just before the end of the tape and round trips that passed through other forms on the way. No round trip ever
  meets a `000`.
- **So:** the machine halts if and only if (observed, not proved) a pulse ever meets an inner `000`. The fuses are
  pure arithmetic; what decides everything is the `00` pulse, a local bouncer of its own that reads the actual words
  near the `00`. That is why the length of the next fuse is not a function of a, b and the block counts: two tapes
  with the same counts and different words give different fuses (`python3 py/pulses.py 'w15 z2 w8 k7 w5' 2 3`).

Next: describe the `00` zigzag as rules over words (it looks like the left-end bouncer again, one level down), and
prove the transparent round trip and the fuse rule in Lean.

```sh
python3 holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD/py/pulses.py 'w15 k9 w8 k7 w5' 1 20   # 1^9 -> 1^6
python3 holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD/py/pulses.py 'w15 z3 w8 k7 w5' 1 20   # 000: halt
gcc -O2 -o defects holdouts/1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD/c/defects.c && ./defects 30000000000 0   # 2.5 min
```

## The pulse in Lean (22 November 2026)

`lean/Pulse.lean` (kernel only: `rfl`, `simp`, `omega`) proves the pulse for every list of words and every tape
around it. Here a word is `01` or `011`, read in the direction of the right sweep:

- `right_words`: in state A the head crosses any list of words to the right, `A> 01 → 11 A>`, `A> 011 → 100 A>`.
- `turn`: `A> 0111 → A> 1110` in 10 steps: three 1s of the run are picked up as a packet `111`.
- `left_words`: the packet crosses the images back to the left and restores every word,
  `11 A>111 → A>111 01` and `100 A>111 → A>111 011`.
- `pulse`: together, `L | A> ws 0111 R → L | A> 111 ws 0 R` in 10·(|ws|+1) steps, for every list ws and all L, R.
  With `R = 1^k 0 …` this is the fuse rule: the run `1^(k+3)` becomes `1^k`, and the words come back unchanged.
- `pulse_halt`: if the words are followed by `0001` instead, the sweep halts the machine (D on a 1).

So two rows of the pulse table are now theorems: a run of three or more 1s after a stretch of words loses three
(`1^3` becomes `00`, the k = 0 case), and an inner `000` followed by a 1 halts. What the packet does at the left end
(where it becomes one more `011` and three more words) and the `00` pulse are not yet in Lean.

**The `00` pulse, as far as it is understood.** The sweep in state A reaching `0 0` writes over it, makes a short
zigzag over the next words, and comes back left over the images in one of three modes, named by the head's state as
it enters each image. `lean/Return.lean` (kernel only, written by `py/ret_rules.py`) proves 21 rules, one for each mode,
image and six-cell carry to its right that occurs on random returns, each for every tape around:

| mode | image `11` (word `01`) | image `100` (word `011`) |
|---|---|---|
| C | becomes `01`; the carry's `011` becomes `101`; stays C | becomes `011`, carry unchanged; stays C |
| E | stays `11`, so the 1s join the run on the right; stays E | becomes `110`, second carry cell cleared; to A |
| A | stays `11`, first carry cell cleared (a run of two); stays A | the head goes right past the carry: a new excursion (open) |

So in mode E a stretch of `01` words becomes one run of 1s: one way a `00` pulse writes a new fuse. All 21 rules
occur on the run from blank tape: in its first 2·10^9 steps the starting pattern of each is met between 96 and
8.3·10^7 times (`c/return_count.c`).

**Mode A at a `011` word starts a new pulse** (`lean/Excursion.lean`, kernel only). The head is then in state A on
the last cell of the image `100`, a 0, and that 0 with the carry after it is a list of words: `011 011` for the carry
`110110`, `011 01 01` for `110101`, and `011 01` followed by `00` for `110100`. So the excursion is an ordinary pulse
over these words to the next defect. If that is a run of three or more 1s, the packet `111` comes back, turns
`10 111` into `11 011` and the head goes on left in mode E (`after_w01`, `after_w011`); `excursion_110110` proves the
whole excursion for the carry `110110` (35 steps). If it is a `00`, a nested `00` pulse starts.

So the return after a `00` pulse is recursive: E merges `01` words into a run of 1s; at the next `011` word the head
switches to A, which turns `01` words into runs of two; at the next `011` word A sends a pulse back right, which
meets the nearest defect (for instance the run E has just made), takes three 1s from it and returns in mode E. A halt
still needs a pulse to meet `0001`; what is open is whether this recursion can ever leave one.

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machines below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in any of the others, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE`](../1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE/README.md): rename A→B, B→C, C→D, D→E, E→A, F→F and exchange left and right; it is this table started in state E, in a mirror
- [`1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC`](../1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC/README.md): rename A→E, B→A, C→B, D→C, E→D, F→F; it is this table started in state B

<!-- end of related machines -->
