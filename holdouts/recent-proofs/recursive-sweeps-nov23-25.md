# What the proofs of 23 to 25 November 2026 teach: recursive sweeps

Between 23 and 25 November 2026, Alex Havrilla (DeepMind) opened busycoq pull requests 110 to 119. Each one decides
BB(6) holdouts: 9 never halt and 1 halts. We compiled all of them here (Coq 8.20.1 on busycoq's BB6 branch, 33209bc,
`Print Assumptions` closed, `coqchk` accepted) and recorded them in `holdouts/external.json` (our PRs #521 and #578).
This note compares each proof with what our folder for that machine had found, and asks where else the method could
work. PRs 110 to 112 are covered briefly at the end, because a project note already describes them.

## The short version

All seven proofs of PRs 113 to 119 have the same shape. Our own work never used it:

1. **Re-read the tape as a list of tokens.** Each proof uses a different token set: three short words (113), 16 blocks
   of 12 to 16 cells (114), or runs of ones each followed by `0` or `00` (115 to 119).
2. **Treat one sweep as a recursive call down that list.** The head goes out to the end of the list and comes back.
   On the way back it hands each token a small *carry*: one bit (114), a remainder mod 3 (115 to 119), or a pair of
   numbers (113). The lemma for one token assumes the lemma for the rest of the list, so a sweep over a list of any
   length is proved by induction on the list. Nobody describes the whole tape as one regular language.
3. **Constrain only what the carry can see.** The invariant says what the *front* of the returned list looks like for
   each carry value, plus one simple condition on the whole list. Everything deeper in the list stays arbitrary.
4. **Glue with a step budget.** `Safe k c` means "no halt within k steps". Strong induction on k closes the outer loop,
   so no closed set of configurations is ever written down.

Our deciders all searched for a closed set of tapes over raw cells: CTL, n-gram CPS, SAT-found automata, and
run-length windows. A recursive sweep with a carry coming back from the far end is invisible to a bounded window. A
closed regular language may still exist (for 114 it does), but it is far larger than anything we searched.

**Five of the seven machines share one core.** PRs 115 to 119 cover two different tables: 115 and 118 are one table,
and 116, 117 and 119 are another. Each proof first maps its machine onto a small "segment stack" machine. Those two
machines differ (4 modes against 6). Both then feed the same recursive sweep (`BigF`/`BigD1`) and the same invariant
library: about 6,100 lines are identical between `M_1RB0LF_…` (115) and `M_1RB1LD_…` (116). Our `related.py` had
grouped the start-state siblings inside each table, but nothing linked the two tables. Our READMEs did describe all
five the same way: a chaotic zone at one end and a long body of the period-10 word `1011011011`.

## Per proof

| PR | machine | our picture before | their tokens | their carry | size, compile |
|---|---|---|---|---|---|
| 113 | 1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RC--- | frozen 001 blocks + a live block (F01); P1 proved in Lean; "maybe Collatz-like, mod 3" | `110`, `100`, `0100` | pair (c, G) with exact division by 3 | 1,127 lines, 5 s |
| 114 | 1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RC--- | 24-cell periodic word with travelling defects; CTL ≤ 5, n-gram ≤ 24 and SAT DFA ≤ 9 all fail | 16 blocks of 12–16 cells, then an end word | one bit | 759 lines, 20 s |
| 115 | 1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE | G08: `(1011011011)^k` plus an irregular region of 156–426 cells | runs `1^(d+1)` closed by `0` or `00` | dlt, branching on dlt mod 3 | 6,985 lines, 90 s |
| 118 | 1RB1RF_1LC0RF_1LE0LD_1RC0LB_---1RA_1LB1RA | G09: same table as 115, started in D | same as 115 | same | same proof, other state names; 81 s |
| 116 | 1RB1LD_1RC0LA_1LA0RE_1LB1LA_1RF0RB_---0LB | G09: bouncer with a moving inner wall, left bursts of 30 cells | runs, as above (6-mode machine) | same as 115 | 7,984 lines, 95 s |
| 117 | 1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA | G08/F08: chaotic zone of 150–630 cells beside a period-10 body; `trip` proved for any body length | same as 116 | same | 7,994 lines, 97 s |
| 119 | 1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC | G08: `A>0 (1101101101)^K Z`, Z irregular, 269–557 cells | same as 116, mirrored | same | 7,982 lines, 94 s |

### PR 113: three tokens and a mod-3 potential

- **Tokens.** The tape left of the head is a word over `110`, `100` and `0100`. A 5-state automaton (`Q5`, `InL`)
  checks that it splits into these tokens. The right side is only the short fixed word `0 1` (or `1`) at the top of each cycle.
- **The recursive sweep (`BoxCPS`).** From `B` at the token word, the head goes in, rewrites the word and comes
  back out in state D or A. The number of tokens stays the same. The contract for a word of n tokens assumes the
  contract for shorter words, and strong induction on n proves them all (`box_cps_holds`).
- **The potential.** `potBits` reads the word token by token and computes a pair (c, G): c counts leading `100`
  tokens and G is a budget. At a `110 100` pair, `step110_100` divides c by 3 and branches on c mod 3. The machine
  can only halt where this function returns `None`, and the invariant c ≤ G (`potBits_c_le_G`) rules that out.
- **Compared with ours.** Our README had the right objects: frozen blocks, one live block, and splits that "depend on
  the sizes modulo 3". It guessed the question might be Collatz-like. The proof shows it is not: a monotone budget is
  enough, and nobody needs to predict exactly when a block splits. We had proved one phase (P1, `p1`, `p1_from0`)
  and planned to chain exact phase maps. That plan needed the exact orbit, which the proof avoids.

### PR 114: a 16-block transducer with a one-bit carry

- **Tokens.** Right of the head the tape is `h1Bits` or `h0Bits`, then a list of blocks from a fixed set of 16
  (`bU`, `bV`, …, `bCC`, each 12 to 16 cells), then `endBits`.
- **The recursive sweep (`BoxStep`).** A in front of a block list runs to the end and comes back in E. On the way it
  replaces each block by another block from the set and returns one bit c (`outCol`). Each block's lemma calls the
  lemma for the rest of the list at most once (`box_cons`). Induction on the length (`box_len`) gives one sweep for
  every list: the set of block lists is closed, and the length stays the same.
- **The outer loop.** Two sweeps (H1 to H0 to H1) add one block at the front (`top_step`). The `Safe` step budget only
  connects these cycles.
- **Compared with ours.** Our "For later" said to tokenize by the 24-cell word, list the defects, and try CTL with
  windows of 24 or more or "a custom automaton built from the word and the defects". That was the right direction.
  The missing ideas: the blocks are not one period of the word, and the carry comes back from the *end* of the list.
  A window cannot know that bit. Over raw cells the closed language is regular, but its automaton needs on the order
  of a hundred states. Our SAT search stopped at 9.

### PRs 115 and 118: the segment-stack machine with a wall (`581`)

- **Tokens.** Each side of the tape is a list. On the left, an entry a stands for `1^(a+1) 0`. On the right, an entry
  (d, b) stands for `1^(d+1) 0`, followed by a second `0` when b is true (`encLeft581`, `encRight581`). In these
  lists the "chaotic zone" and the period-10 body are one list of short runs.
- **The abstract machine.** `step581` has 4 modes (F moving right, B moving left, D either way) and about 30
  rules. Each rule is checked against the machine in one lemma (`step581_sound`).
- **The wall.** After 803 abstract steps the left list is the fixed word [1; 3; 2], and from then on the left side
  only reflects (`wall_9`, `wall_15`, `wall_27`). Each reflection launches one sweep over the whole right list.
- **The recursive sweep (`BigF`, `BigD1`).** These are two mutually inductive relations. A segment's output depends
  on the carry dlt that comes back from the rest of the list, and splits three ways on dlt mod 3 (`BF_*_rem0/1/2`).
- **The invariant.** `InvAt m` is a record of 27 facts, proved together by strong induction on the recursion depth m.
  Each fact is of the form "if `BigF` returns dlt = 2, 5 or 8, the output starts with `(0,true) (1,false) (1,false)`".
  The other definitions are shape predicates on the front of the list (`Good1`, `Good2` with 18 cases, `SafeU`,
  `Zero111` and others) and one global condition (`NoNonlast0F`: no `(0,false)` entry except possibly the last).
  `StrongWall` closes: it shows that every reflection returns dlt ≡ 1 (mod 3), the one residue for which the proof
  (`wall_no_halt_of_bigF_inv`) can step past the wall again.
- **Compared with ours.** Both READMEs proved the sweep rules over the periodic part (`pass_right`, `pass_left` and
  `cross_D` for 115; the sweep rules of 118). Both treated the irregular region as noise of bounded size. It is not
  bounded noise. It is the front of a stack whose recursion has only three carry classes.

### PRs 116, 117 and 119: the same core reached from a 6-mode machine (`484`)

- `State484` has 6 modes and lists of (count, separator) entries on both sides (`stepAtomic`, 24 cases checked in
  `stepAtomic_sound_*`). The three machines differ only in the state names and, for 119, a mirror (`enc505`,
  `enc689`). That matches our `related.py` finding that they are one table started in A, B and C.
- From the start, 315 abstract steps reach the wall configuration `mAL [(2,false)] …` (`tm505_reaches_entry`,
  checked by `vm_compute`). The 6-mode machine's sweep (`EvalF`, `EvalDL`, `Disp`) is matched to `BigF`/`BigD1` by a
  bounded-horizon bisimulation (`horizon_bisim`). After that, the 581 invariant library is reused unchanged.
- **Compared with ours.** For 117 we had proved `trip`, which says one round trip leaves the cells next to the zone
  the same whatever the body length. We read that as "a mirror whose length does not matter". In the proof the body
  is not a mirror. It is the deep part of the stack, which the invariant leaves arbitrary. For 116 we saw a moving inner wall and
  left bursts of 30 cells; we did not check how these map onto the stack.

### PRs 110 to 112, briefly

- **110** (1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF and 1RB0RA_1RC0RD_1RD0LC_1LE1RA_---1LF_1RB0LC): a counter of
  eras feeds a fixed stream of events to the messy right end. The right end is then handled column by column with two
  small transducers and a rational potential (`2p ≤ 3g + 3`). Both machines reach the same configuration family, so
  one proof core covers both.
- **111** (1RB0RC_1RC1LB_1LD1RA_1LE0LB_---1LF_0LF0LC, halts after about 1.87·10^54 steps): a run-length stack simulator
  with binary counts, plus closed-form countdown eras, evaluated by `vm_compute`.
- **112** (1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LF---_1LB1RF): tokens `1` and `10`, a 10-state automaton over pairs of tokens,
  and 18 assume-guarantee contracts closed by strong induction. This is the first proof of the recursive-sweep shape.
  Our attempt to transfer it (project note `pr112-technique-adaptation.md`) looked for a DFA of tapes and failed. In
  hindsight the transferable part is the recursive contract, not the automaton.

## Can the method transfer? What we checked (25 November 2026)

Everything below is computed, not proved. The script is `tools/segment_match.py` in this folder.

- **Exact reuse of the 581 or 484 core.** `segment_match.py` takes a machine and tries every state assignment and both
  mirrors. It runs each rule of `step581` and `stepAtomic` on 60 random small stacks and checks that the machine
  reaches the encoded result. It recovers the five proved machines with the right renamings (115: F, B, D; 118: B, C,
  A; 116: B, C, E, A, D; 117: A, B, E, C, D; 119: C, A, E, B, D, mirrored). Among the 509 holdouts not yet decided,
  **none matches**, and none passes more than 67% of the rule tests. That 67% plateau comes from the crossing rules
  that many machines share. So the existing Coq core does not apply to any other holdout as it is.
- **Close tables.** No undecided holdout is within 3 changed transitions of any of the seven tables, under any
  renaming or mirror. The closest are 4 transitions away: 1RB0LC_1LC0RE_1LD1LB_1LA1LD_1RF0RA_---1RE,
  1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA and 1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB (from 116), and
  1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF (from 112).

So the transfer has to be of the *method*: tokens, a recursive sweep with a small carry, and an invariant on the front
of the list. It cannot be the proof text. The candidates for each variant, from our own folder descriptions:

| variant | why it fits | candidate holdouts |
|---|---|---|
| segment stack + wall + carry mod 3 (115–119) | runs of ones split by `0`/`00`, a chaotic zone beside a periodic body | 1RB0LD_0RC1RA_1LD1RC_1LE0RF_---1LA_1LF0LA (51-cell word, irregular zones at its ends); 1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF (blocks of 1s merging and splitting); 1RB0LC_1LC0RE_1LD1LC_1LA1RD_1RF1RB_---0RB (blocks of 1s split in halves and thirds, table close to 116); 1RB0RA_1RC1RF_1LD0LC_1RA1LE_1RA0LC_---0RD (chaotic control word) |
| finite block set + one-bit carry, closed by induction on length (114) | a periodic background with defects that travel | 1RB1RE_1LC1RC_0RF1LD_1LE0LB_1LB0RA_---1RA (11110 blocks, travelling defects); 1RB0RF_1LC0RA_0LD0LB_1RD1LE_0RC0RA_1RA--- and 1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA--- (defect gas over a 10 background); 1RB0RC_1LC1LA_1RD0LB_1RE1RC_1RA0RF_1RC--- and 1RB0RF_1RC0RD_1LD1LB_1RE0LC_1RA1RD_1RD--- (drifting defects); 1RB0LD_1LC1RE_1LA1RC_1RA0LC_0RF---_0LD1RB (travelling defects in a 1^8 background) |
| short tokens + a potential with division by 3 (113) | frozen blocks and one live block (F01) | 1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB--- (frozen blocks, last block growing about 1.4× per sweep, the model the F09 screen compared 113 to); 1RB0LA_0LC0RA_1LA1LD_1LC0LE_1RF0LF_0RB--- (domain builder) |
| recursive contracts on token pairs (112) | chaotic bouncers with bounded crossings per sweep | the 8 G08 machines listed in `pr112-technique-adaptation.md` |

## What to build next

1. **Derive the segment machine automatically.** `step581` and `stepAtomic` are just the machine run on run-length
   tapes, with one rule for each (mode, front entry) case. A tool could build that table for any holdout by symbolic
   execution, for entry counts up to a bound plus one generic rule with "d ≥ k". That would give every run-of-ones
   holdout its own exact abstract machine to study.
2. **Learn the carry.** Over the derived machine, record for each sweep the pair (input list, returned carry), and
   search for a small set of carry classes (a remainder mod m, or one bit) that predicts the front of the output.
   That is what `InvAt` writes down by hand.
3. **Search for block sets with a sweep carry (114 style).** Cut the tape into blocks and check whether one sweep maps
   every block to a block of the same set and returns a bounded carry. This is a closure check on a finite alphabet,
   which we can automate and then print as Coq in the `box_*` form.
