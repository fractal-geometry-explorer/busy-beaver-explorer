# Halting copies against merging copies (27 November 2026)

Technique B of the second brainstorm (`technique-brainstorm-2-nov27.md`): the ensemble check of
[`halt-hunt-ranking-nov26.md`](../halt-hunt-ranking-nov26.md) saw 49 halts among 1,000 moved copies of orbit states
of 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE where about 340 were estimated, and the survivors sat on a few orbits.
Fit a predicate that separates the halting copies from the merging ones, and look for an invariant in it.

**Result: there is nothing to fit, and the reason is general.** Nothing was decided.

## What was done

Both target maps are low-dimensional, so the copies were replaced by every state there is.

- 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE: all 2.7·10^8 tapes B(x, y) below level 2x + y = 32,768, followed
  forward (`c/fates.c` in its folder), and every halting tape of the levels up to 4·10^6 followed backward
  (`c/back.c`). The two agree exactly where both exist.
- 1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD: all 2.7·10^8 zigzag starts below level 16,384, forward (`c/fates.c`
  in its folder).

Details and tables are in the two machines' READMEs, sections "Halting copies against merging copies".

## What it shows

1. **Merging is counting, not protection.** Each map is two-to-one on reachable states (for the first machine this
   is in Lean, `lean/Merge.lean`: three tapes lead to a tape with x and y even, one to a tape with y odd, none to x
   odd), while a level holds a number of states proportional to the level and one step raises the level by a few.
   So the states of one level, k steps later, sit on a number of states that shrinks like 1/k. All 139,136 tapes
   (x even) of levels 2048 to 2303 of the first machine are on 2 orbits by level 32,768, apart from the 0.5% that
   halt; all 17.8 million starts of levels 8192 to 9215 of the second are on 47 orbits by level 16,384.
2. **The low count was the population figure.** Of all tapes of the levels where the probe's copies started (about
   560 to 2,240), 5.1% halt below the level where it stopped (about 18,000), and the others are on 3 orbits. The
   probe found 4.9%, and its longer run 3 orbits. The copies near the orbit were typical tapes.
3. **Averaged over scales, the estimate is right.** The fraction of all states of levels [L/2, L) that halt in
   [L, 2L) swings between 0.1% and 31% for the first machine (mean 8.6% over 16 octaves; estimates 8 to 11%) and
   between 2.3% and 15.2% for the second (mean 8.7% over 10 octaves; estimate 9 to 12%). One halting tape can take
   31% of an octave. An ensemble of any size is two or three trials per octave.
4. **No predicate.** Trees of depth 3 and 6 and a forest, on residues, ratios and tent digits, score 50 to 54%
   balanced accuracy on held-out levels, for halting against surviving and for joining the blank-tape orbit against
   joining another (`py/contrast.py` of the first machine). The first test asked for under 1% errors at depth 3.

## What this means for the other targets

The five further targets of technique B were chosen because their rate drops when parities are kept; that is a
residue effect and was known. For any map of this kind (expanding, a few-to-one, sizes growing by a bounded amount
per step) the ensemble check measures the fate of a few orbits and cannot confirm or refute a rate, and a contrast
of halting against surviving copies contrasts the ancestors of one or two halting states with everything else.
What remains true and usable:

- The halting rate should be measured on *all* states of a level (exhaustively, or backward from the halting
  states), over many octaves. Both machines pass that test, so their halt estimates stand: about 3.75 and 2.9
  expected halts so far and none seen (chances of about 2.4% and 5%), with one orbit each.
- The blank-tape orbit of the first machine is the largest orbit for every start level tried from 128 up (38 to
  77% of all tapes join it); for the second machine it is a small one (2 to 9%). Neither is distinguished by anything found
  here other than not having halted.
- A proof of non-halting would have to show that no halting state has the start among its ancestors. The ancestor
  trees are critical branching (one reachable ancestor per generation on average, by counting parities): most die within a few generations, a few
  never do, and which is which looks as irregular as the orbit itself.
