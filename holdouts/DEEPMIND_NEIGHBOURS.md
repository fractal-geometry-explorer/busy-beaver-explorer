# Holdouts one transition from a DeepMind non-halting proof

Google DeepMind has proved many BB(6) tables never halt: 161 modules in
[google-deepmind/cryptids](https://github.com/google-deepmind/cryptids) (`BusyBeaver/BB6/NonHalt`, commit `3647718`)
and the Rocq proofs in their busycoq pull requests (23, 47 to 54, 56, 67, 68, 78 to 80, 85 to 87, 90, 92, 95, 96).
Together that is 184 distinct tables (`tools/deepmind/neighbours/nonhalt_tables.txt`). Can a holdout that is one
transition away from one of them be settled by changing their proof a little? This page reports the search
(18 November 2026). All credit for the proofs it starts from goes to DeepMind.

**Result.** 10 open holdouts are one transition away from a DeepMind table, up to renaming states, exchanging left and
right, and starting in another state. They form 4 tables. None of DeepMind's proofs carries over unchanged. For one
holdout, Lean now proves that it halts exactly when DeepMind's table, started in another state, halts. For the
others the search found exactly which of DeepMind's lemmas fail and why.

## Method

`tools/deepmind/neighbours/screen.py` renames the states of each of the 608 holdouts in all 720 ways, with and
without a mirror, and looks for a DeepMind table that differs in at most one of the 12 transitions. The holdout's start
state may become any state, so a match can be "DeepMind's table with one transition changed, started elsewhere".
The output is `tools/deepmind/neighbours/neighbours.json`. 30 holdouts are DeepMind's own proved machines. 10 others
are one transition away.

For each match, DeepMind's step lemmas were run again by simulation on the holdout's table. These are the lemmas
their Lean proofs check by `execute` or `decide` on tapes with symbolic ends. `seg.py` runs a machine from such a
configuration and fails if it reads the symbolic part. `vkq.py` and `u3.py` restate two of their proofs' lemma lists.
On DeepMind's own tables every lemma passes, which checks the restatement.

## The four tables

### 1RB0LD_1LC1RE_1LA1RC_1RA0LC_0RF---_0LD1RB: a reduction proved in Lean

DeepMind proves `1RB1RE_1LC1RB_1RA0LD_1RC0LB_0RF---_0LD1RA` never halts from state A, with a large run
certificate (`M_1RB1RE_1LC1RB_1RA0LD_1RC0LB_0RFHHH_0LD1RA.lean`, 18,380 lines: macro rules, 46 run chunks and a final
"glider" configuration). Started in state C instead, with states renamed to tree normal form, that table is
`1RB0LD_1RC1RE_1LA1RC_1RA0LC_0RF---_0LD1RB`. That machine is not on the list. The holdout differs from it only in
B0 (`1LC` against `1RC`).

- B is entered only by `1RB`, so whenever the machine is in B the cell to its left is 1. Where the other machine does
  B0 in one step, the holdout does `1LC` and then C1 (`1RC`). It is then in the same configuration after two steps.
- In 4·10⁸ steps the two runs give the same tape at all 9,783 F0 events, with the holdout about 9% slower.
- **Lean proof:** `holdouts/1RB0LD_1LC1RE_1LA1RC_1RA0LC_0RF---_0LD1RB/lean/SyncDM.lean`, `halts_iff`. It is a
  re-sync certificate (`TM.Sync`, found by `tools/py/syncpair.py` with windows of 2 cells, 67 abstract
  configurations) and checks in 3 seconds. It states that the holdout halts from blank tape if and only if
  `1RB0LD_1RC1RE_1LA1RC_1RA0LC_0RF---_0LD1RB` does.

This does not settle the holdout. DeepMind's certificate starts from state A. The runs from A and from C never share a
configuration at F0 events in 4·10⁸ steps. DeepMind's macro rules are facts about the table, so they hold for both
starts. What is missing is a new run certificate from state C, which needs their search tool or a reimplementation of
it.

### 1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA0RF_0RA--- and its three other starts

The holdouts are `1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA0RF_0RA---`, `1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---`,
`1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---` and `1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB---`. They are one table
started in four states. DeepMind proves the neighbouring table `1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA1RF_0RA---` from all
four starts. Their proofs use the word calculus `WordVKQ` (`Calculi/WordCalculusF.lean`, `WordCalculusG.lean`). In it,
the tape right of the head is a list of words V, K, Q and primed copies. A pass through the tape is a sequence of
calls that obey 12 segment rules (`SegSpec`). A potential argument on the word list (`Traj114.Good`) shows that the
passes go on forever.

The holdout changes E1 from `1RF` to `0RF`.

- 11 of the 12 segment rules still hold.
- The rule `seg_ca_V` (one `ca` call on V gives one `ch` call and leaves Vp) becomes `[ca] → [ch, ca, ca]`, through
  the left words `0001`, `0111` and `0101`, still leaving Vp. So each such segment makes three calls instead of one.
- Two of the seven turnaround pieces (`zP0`, `zP4`) also fail, because the left end of the tape is built differently.

DeepMind's potential argument counts calls, so it would have to be redone for the new call pattern. That is a new
proof, not an edit.

### 1RB0LC_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD--- and 1RB0RE_1LC0RD_1LD0LD_1RA0LC_1RA1RF_1RA---

These two holdouts are one table started in two states. DeepMind proves the neighbouring table from four starts. All
four proofs go back to `M_1RB0LD_1RC0RE_1LD0RE_1LA0LA_1RB1RF_1RBHHH.lean`. Its model is a stack of counters on the
left and items `00`/`01` on the right (`cfgC`, `cfgD`, `cfgE`), with 11 macro rules and a numerical invariant. In that
frame the holdout changes C1 from `0RE` to `0RA`.

- Every macro rule still holds except where it produces an E configuration with counter 0. These are `step_D0`,
  `step_C_nil_item00_to_E` and `step_D1` with c = 0, and `step_E3` with c₂ = 0 (`u3.py`).
- The reason: after C1, if the next cell is 0, the two machines agree again one step later (E0 = A0 = `1RB`). If it
  is 1, DeepMind's machine goes E1 → F. This is one of its two routes into F, the state whose 1-transition halts.
  The holdout does A1 (`0LD`) instead.
- So the holdout never takes this route into F. From the c₂ = 0 case of `step_E3` it runs for hundreds of steps
  without returning to one of DeepMind's configuration forms.

New macro rules for counter 0 would be needed, and then a new invariant.

### 1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB---, 1RB0RE_1LC1RA_1LD0LC_0RE0LA_1RA1RF_0RA---, 1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE

One table, three starts. It is one transition from three DeepMind tables, which differ from it in the same slot
(`1LA`, `1LB`, `1RB` in place of `0RA`). DeepMind's own repository classes these three holdouts as cryptids
(`Accelerations/…`, kind `cryptid`), so they were not attempted here.

## Reproducing

    python3 tools/deepmind/neighbours/screen.py BB6_holdouts_608.txt tools/deepmind/neighbours/nonhalt_tables.txt out.json
    python3 tools/deepmind/neighbours/vkq.py 1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA1RF_0RA--- 1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA0RF_0RA---
    python3 tools/deepmind/neighbours/u3.py 1RB0LD_1RC0RE_1LD0RE_1LA0LA_1RB1RF_1RB--- 1RB0LD_1RC0RE_1LD0RA_1LA0LA_1RB1RF_1RB---
    holdouts/1RB0LD_1LC1RE_1LA1RC_1RA0LC_0RF---_0LD1RB/lean/check.sh
