# invariant-transfer: do the invariants of proved machines hold on open holdouts?

This is technique D of [`../technique-survey-nov26.md`](../technique-survey-nov26.md), run on 26 November 2026.
**Nothing was decided.** Three screens were run over all 509 open holdouts against 236,071 proved tables. Each one
ends at the same wall: where a holdout is close to a proved machine, the two part exactly at the rare event that
decides the holdout. The screens, their data and the tools are kept so that nobody has to run them again.

Evidence levels: the tables and counts are computed (plain simulation, trusted C and Python). The certificate runs
use busycoq's verified deciders in Coq 8.20.1, so a PASS there would have been a proof. There was none.

## The pool of proved machines

| source | tables | how the invariant can be used |
|---|---|---|
| busycoq, `BB6` branch of our fork (commit `4e86645`), every table named in `verify/*.v` outside the `Eqv*` files and not itself a holdout | 235,923 | for those decided by `solve_cert` (about 203,000 uses in the files), the invariant is a closed tape language that the decider recomputes from its parameters; the rest are template or one-off proofs |
| DeepMind's non-halting tables (`tools/deepmind/neighbours/nonhalt_tables.txt`) | 184 | Lean, one invariant per file |
| holdouts decided in this repository (`status.json`) | 99 | Lean or Coq, one per folder |

The `Eqv*` files were left out because they state equivalences between machines, not proofs. `CubicCap.v` names four
open holdouts in mirrored form (`Cert_WF` statements about their arithmetic maps); these are not proofs either and
are marked as such below.

Tables are compared up to a renaming of the states and a mirror, and with any start state where that is said.

## Three facts that shape the screens

1. **"The holdout stops using a transition" adds nothing to a late start.** Suppose a holdout stops using some
   transitions after step T. Treating those transitions as halting and running a closed-set decider from the
   configuration at step T can only shrink what the decider proves: the closure is the same set, with more halts in
   it. So the screen "eventually unused transitions" is the screen "run the decider from a late configuration".
   busycoq's deciders already take that late start as their first parameter (`simT`; upstream certificates use up
   to 100,000,001 steps), so its authors have run this screen in part.
2. **A proved machine that fills in the holdout's halting transition says nothing.** Such a machine follows the
   holdout until the holdout halts. It is proved never to halt, but its closed set contains the holdout's halting
   configuration; if it did not, the same decider would prove the holdout. 41 of the one-transition pairs are of this
   kind and were dropped.
3. **If a neighbour's closed set excluded the splitting context, the holdout would already be decided.** Say the
   holdout H and the proved machine P differ in one transition and re-join after every split as long as a local
   context holds (for example "a 1 to the right"). If P's closed language L contained no configuration in the other
   context, L together with the detour configurations would be closed under H's steps and free of halts, so H
   would be decidable by an automaton of about the same size. All such pairs below are famous holdouts, so P's
   language must contain the bad context, and what transfers is only a reduction: *H can halt only after the bad
   context has occurred*.

## Screen 1: the same table started in another state

41 open holdouts have the complete table of a proved machine, started in another state: 25 of them have a
never-halting sibling (42 pairs) and 16 a halting one (17 pairs). The list is in
[`../tools/transfer/data/same_table_siblings.json`](../tools/transfer/data/same_table_siblings.json). A sibling's closed set is
closed under the holdout's steps, since the table is the same, so the holdout never halts if its run ever enters it.

- **Do the runs merge?** `merge.c` hashes every configuration of both runs relative to the head and samples by the
  hash alone. In 10^9 steps of each run, none of the 64 pairs (59 with a proof and the 5 `CubicCap` entries) shares
  a configuration.
- **Does the holdout's run enter the sibling's closed set?** For the 31 never-halting pairs proved by `RWL_mod`,
  `CPS_LRU` or `NG`, the sibling's own certificate was run on the holdout from late configurations (`simT` near
  1,001 and 100,001, with the two window lengths also exchanged for mirrored pairs, and at every block phase when
  the block size is at most 4). A late configuration inside the sibling's set would make the certificate pass,
  because the closure from a configuration inside a closed set stays inside it. Of 145 runs, 128 fail and 17 run out of memory; none passes
  ([`sibling_cert_sweep.txt`](../tools/transfer/data/sibling_cert_sweep.txt)). The 17 belong to five pairs with very large certificates (windows of 100,000 to 400,000), on
  1RB0RE_1RC0RE_1LD1RB_1LA0LA_1RF0LC_---0RC, 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE, 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC and
  1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD; they also run out of memory with 10 GB, so these five pairs are untested.
- The 7 pairs proved by the `_FAR` deciders have no late-start parameter; their certificates fail on the holdout
  from blank tape. The inductive decider that proves three siblings of
  1RB---_1RC0LD_0LB0RE_1LB1LC_1RD1RF_1RD1RA fails on the holdout with the budget (100,000) at which it proves a sibling in 8 seconds,
  and gives no answer in 9 minutes with 3,000,000.

Limits: Coq simulates the prefix at about 19 microseconds a step, so late starts beyond 10^6 steps were not tried.
A native decider that reads a configuration from a file would lift that limit. One certificate
(`CPS_LRU 100000001 400000 400000 8 …`, the sibling of 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD,
1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE and 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC) needs more than the 5.5 GB
a run was allowed here.

## Screen 2: transitions a holdout stops using

`usage.c` ran each of the 608 machines for 3·10^9 steps and recorded, per transition, the number of uses and the
last use. 106 of the 509 open holdouts have at least one transition that is used and then not used again before the end of the run, 195 transitions in all ([`quiet_transitions.json`](../tools/transfer/data/quiet_transitions.json)). 102 of the 195 are used fewer than 10 times and 60 between 10 and 99 times. Only 18, on 9 holdouts, are used more than 1,000 times before they go quiet, for example E1 and F1 of 1RB---_1LC0RB_0LD0LC_1RE1RB_1RD1LF_1LA0LE (about 105,450 uses each, none after step 1.49·10^9) and A0 of 1RB1LC_1LA---_1LD0LA_1RE0LE_0RF1RE_1LB1RD (57,279 uses, none after step 3·10^6).

The quiet transitions are rare events, not abandoned ones. A typical case is
1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LA---: D1 and F0 are used 16 times, at steps 836, 841, 846, 1,888, 4,297, 8,599,
8,724, 106,357, 276,462, 526,320, 1,102,944, 20,682,795, 62,482,997 and 136,905,559. The gaps grow, and the next use
is simply beyond 3·10^9. These are the F-events of the nested-counter families. Their one-transition neighbours are
proved (many by the inductive decider) precisely because they do something harmless at that event.

By fact 1 the test for a truly abandoned transition is a late-start decider run. With the quiet transitions treated as wildcards, 85 holdouts agree with 4,284 proved tables elsewhere, 1,192 of them with the start state kept ([`quiet_matches_summary.json`](../tools/transfer/data/quiet_matches_summary.json)). Those pairs were **not** tested further here: the late start would have to lie beyond 10^6 steps (for the nine heavy cases beyond 10^9), which Coq cannot simulate in reasonable time. This is the one part of the technique left open, and it needs a native late-start decider first.

## Screen 3: run the holdout and a proved neighbour together

`near1.py` and `near2.py` list every proved busycoq table that differs from an open holdout in one or two
transitions, with the start state kept: 741 pairs at distance one (211 holdouts) and 1,398 at distance two (294
holdouts), 2,138 after removing duplicates. `lock2.c` runs both machines from blank tape. While they would write the
same symbol and move the same way they step together; when they part it looks for the first moment, within 80 steps
of each, at which tape and head agree again.

2,128 pairs part within 10^8 steps and never re-join. Nine stay together:

| holdout | neighbour (in the holdout's state names) | differs in | splits re-joined | what the neighbour is |
|---|---|---|---|---|
| 1RB1RA_1RC1LB_1LD0RA_1LB0LE_1LF1LD_---0LD | 1RB1RA_1RC1LB_1LD0RA_1RB0LE_1LF1LD_---0LD | D0 | 2,733 in 2·10^10 steps | never halts (`FARv3.v`, `RWL_mod_FAR 2000 1000 1 3200 2 4 1 0`) |
| 1RB1LF_1LC0RD_---1LA_0LA0RE_1LA1RA_1LB0LD | 1RB1LF_1LC0RD_---1LA_1LE0RE_1LA1RA_1LB0LD | D0 | 2.0·10^9 in 2·10^10 steps | never halts (`FARv3.v`, `RWL_mod_FAR 60000 30000 2 3200 2 2 3 0`) |
| 1RB0RF_1LC1LF_1RD1LC_---1RE_0RC1RF_1RA0LB | 1RB0RF_1LC1LF_1RD1LC_---1RE_1RD1RF_1RA0LB | E0 | 199 in 2·10^10 steps | halts (`RRBAHaltv1.v`) |
| 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE--- | 1RB0RE_1RC0RA_1LA1LD_1LC1LF_0LC0LD_1LE--- | B0, E1 | 9 in 10^8 steps | halts (`IndHaltv1.v`, as 1RB0RD_1RC0RA_1LA1LE_0LC0LE_1LC1LF_1LD---) |
| 1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC | 1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA1LD_---0LC | E1 | 3.3·10^9 in 2·10^10 steps | not a proof (`HaltingCryptidCandidate1.v`; busycoq's `Eqv_Misc.v` already relates the two) |
| 1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE, 1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE, 1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE, 1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE | tables named in `CubicCap.v` | one transition each | millions in 10^8 steps | not proofs (`Cert_WF`); the known cubic-cap family |

What the first four mean:

- **1RB1RA_1RC1LB_1LD0RA_1LB0LE_1LF1LD_---0LD.** The holdout does D0 = `1LB`, the neighbour `1RB`. If the cell
  to the right of D is 1, the neighbour takes two more steps (B1 `1LB` twice) and is where the holdout is after one
  step. If it is 0 the two part for good. In 2·10^10 steps the cell is always 1. So from blank tape **the holdout's
  run is the neighbour's run with two-step detours removed, until D first reads a 0 with a 0 to its right, and the
  holdout cannot halt before that**: a halt in step with the neighbour would be a halt of the neighbour, which is
  proved impossible. The neighbour's invariant is tiny (each side summarised by its nearest run of equal cells: the
  symbol, whether the run has at least 2 cells, and its length mod 4). By fact 3 it must contain the bad context.
  The folder of this machine already has a sharper reduction in Lean (`halts_only_at_front`), so this is a second
  view of the same rare event, not a new result.
- **1RB1LF_1LC0RD_---1LA_0LA0RE_1LA1RA_1LB0LD.** The holdout does D0 = `0LA`, the neighbour `1LE`. With a 0 to the
  left of D the holdout takes four steps (D0, A0, B0, C1) and the neighbour two (D0, E0) to the same configuration.
  With a 1 to the left they part. So **this holdout cannot halt before D reads a 0 with a 1 to its left**, and
  until then its run is the neighbour's. The split happens about once every ten steps, so the neighbour, proved
  never to halt, follows the same 4/3 Collatz-like orbit for as long as the holdout's tail stays harmless.
- **1RB0RF_1LC1LF_1RD1LC_---1RE_0RC1RF_1RA0LB.** The neighbour (E0 = `1RD`) is proved to halt, in D on a 0. With a
  1 to the right of E the two re-join (three steps against one). With a 0 there the neighbour halts on the next
  step. That is the neighbour's only way to halt: it enters C only while moving left, so the cell to the right of C
  has just been written as 1, and D after C0 never reads a 0. The neighbour does not halt within 2·10^10 plain
  steps; its halt is proved by accelerated simulation (`solve_halt' 50000 10000`, 44 seconds here). So **the
  holdout does not halt before the neighbour's halting time and then stands on the neighbour's last
  configuration**: E on a 0 with a 0 to its right. Evaluating the same verified simulator to its end gives that
  configuration: eight or more 1s to the left, and `0 1 0 1 0 1 0` from the cell right of E on. The holdout then
  does E0, C0, and D reads a 1, so it does not halt there and goes on. The same accelerated simulation run on the
  holdout itself gives no answer in 15 minutes. This is the picture of 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF and
  busycoq PR 93's machine: the holdout goes on where its neighbour halts. The step at which the neighbour halts was
  not computed (the simulator does not count steps), so the bound "no halt before then" has no number yet.
- **1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---.** The same picture at distance two. Its distance-one neighbour
  1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1RA--- halts at step 23,523,821; the pair is in step through seven splits and
  parts at the holdout's step 23,492,737.

Two more near misses show the same thing. 1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE--- is in step with the halting
machine 1RB1RD_1LC0LE_1LA0LB_1RA1RF_0RA0RD_1RE--- until step 6,518,683, which is 22 steps before that machine halts.
And re-running the DeepMind tables and our own decided holdouts as neighbours (22 open holdouts within one
transition) gives no pair that re-joins at all.

## What this says about technique D

- The table-level form of the idea is exhausted for busycoq's pool: every proved table within two transitions of an
  open holdout (start kept) has been run against it, and every same-table sibling has been tested for a merge and
  with its own certificate.
- Where a proof almost transfers, the holdout and the proved machine are the same until one specific local
  context, and the proved machine either does something harmless there (never halts) or halts there (the holdout
  goes on). That context is the open question itself. No regular invariant of the neighbour can exclude it (fact 3).
- What does transfer is a **reduction with a regular side condition**: until the context occurs, the holdout's
  configurations lie in the neighbour's closed language. For the two never-halting neighbours above this could be
  stated in Lean as a one-way version of `TM.Sync` (the neighbour may halt, the holdout may not leave). It was not
  written, because both folders already hold stronger Lean reductions.
- A by-product that other work can use: Coq 8.20.1 installs here in about a minute with
  `nix profile install nixpkgs#coq_8_20`, busycoq's decider library (`CTL62.v` and what it needs) compiles in 20
  seconds, and `runcert.sh MACHINE "CERT"` then runs any `solve_cert` certificate on any machine.

## Reproducing

See [`../tools/transfer/README.md`](../tools/transfer/README.md).
