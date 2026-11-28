# Alk's warm-start history n-gram proof (busycoq PR #121), 28 November 2026

busycoq pull request #121 (Alk, 27 November 2026, open) proves in 58 lines of Rocq that
1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF never halts. The same machine was proved before by DeepMind (cryptids pull
request 42, 1,693 lines of Lean, see [`../cryptids-pr42-nov27.md`](../cryptids-pr42-nov27.md)) and re-proved here by
two search tools ([`token-grammar.md`](token-grammar.md), [`frontier-window.md`](frontier-window.md)). This note
explains what Alk's proof does, why it works where busycoq's own deciders failed, and whether it transfers.

**In short.**

- The proof is busycoq's existing n-gram decider with tape histories (`NG`, the decider of `NG_v1.v`), with one
  change: the history-augmented machine is run for 30,000 steps from blank tape, and the closure starts from the
  configuration it reaches, **histories included**. The original decider starts from blank, or runs the plain machine
  first and then starts with every history empty. That change is the whole proof; the soundness lemma is 20 lines that
  reuse existing busycoq lemmas.
- Both halves are needed. Re-implemented here (`wng.cpp`, below), the warm start closes for 21 of 40 settings tried
  and from every start time from 16,423 steps on; the same settings from blank tape, or with the warm start but no
  histories (windows up to 12), never close.
- The closed set is small and tight: 14,630 local configurations over 1,928 tape symbols, and the same set from every
  start between 25,000 and 1,000,000 steps. 1,752 of the 1,928 symbols are written by the real run between steps
  30,000 and 200,000. So it is an invariant of the machine's steady state; the first 16,000 steps only add symbols
  that let the abstraction reach the halt.
- Alk's likely starting point is that busycoq already proves the same table from two other start states
  (`NG_v1.v`, `nonhalt12951` and `nonhalt13144`, renamed and mirrored). We searched busycoq's 583 Rocq files the same
  way: **24 open holdouts have a same-table sibling that busycoq proves non-halting** (table below), 16 more a halting
  sibling. None transfers: the `NG` sibling's settings fail on its holdout, warm or cold, and busycoq's `CPS_LRU` and
  `RWL_mod` deciders (re-implemented here, reproducing all 19 sibling proofs) fail on their 20 holdouts from starts
  of 10^3 to 10^7 steps.
- Screen of the 501 open holdouts with the warm start, 90 settings each: see [the screen](#screen-of-the-501-open-holdouts).

## The proof

`verify/M_1RB0RC_1LC0RB_1LD0LD_1RA1LE_HHH0LF_1LB1LF.v` (copy in the project files, `busycoq-prs/121/verify/`):

```coq
Definition hist_decide (tm: DHTMFromTM.TM.TM) (simT maxT maxS NG_n len1 len2 LRU_n: N) : bool :=
  let upd := TapeHistoryImpl.QSym_history_upd (N.to_nat len1) (N.to_nat len2) (N.to_nat LRU_n) in
  let tm1 := TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.map_TM tm upd in
  match TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.TapeHistoryTM.DH_cconfig_steps tm1
          TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.TapeHistoryTM.cc0 simT with
  | inl c1 => CTL_NG_QSym.CTL_decide_nonhalt tm1 c1 {| len := NG_n; maxS := maxS |} maxS (maxT*100)
  | inr _ => false
  end.
...
Theorem nonhalt: ~halts tm c0.
Proof. rewrite halts_halts'. eapply (hist_decide_spec _ 30000 30000 30000 3 12 2 0). vm_cast_no_check (eq_refl true). Qed.
```

Compare busycoq's own `NG` case in `CTL.v`: it runs `DHTM.DH_cconfig_steps tm cc0 simT` (the plain machine), then
`inv_map_cconfig c` puts an empty history on every cell. In `NG_v1.v` all 13,762 uses have `simT = 0`.

**What the pieces are** (all in `verify/CTL.v` on the BB6 branch):

- *Tape symbols with history.* A cell is (bit, list of (state, bit read) pairs, newest first). When the head
  leaves a cell it prepends the pair it just read. `QSym_history_upd len1 len2 LRU_n` keeps the newest `len1` pairs
  exactly and compresses the rest to `len2` entries by a least-recently-used rule. Here: 12 exact visits and 2 more.
  An unvisited cell is (0, empty), which no visited cell can equal.
- *The closed tape language.* `CTL_NG_QSym` is busycoq's generic CTL search with an n-gram automaton on each side:
  the state of a half tape is its `NG_n` symbols nearest the head (here 3) or, if it has fewer, all of them, which
  keeps the far blank end exact. The search closes a set of (state, direction, left state, right state) under steps,
  guessing the next cell from the transitions recorded so far. It is the NGramCPS decider of the Coq-BB5 paper, with
  windows of 3 rich symbols instead of many bits.
- *Soundness.* `hist_decide_spec` chains three existing lemmas: the history machine simulates the plain machine
  (`map_nonhalt`, `inv_map_nonhalt_c0`), running it `simT` steps is sound (`DH_cconfig_steps_spec`,
  `evstep_nonhalt`), and the CTL search is sound from any start configuration (`CTL_decide_nonhalt_spec`). Nothing
  new had to be proved; the generic search never required the start to be blank.

## Reproduction (`../tools/warm-ngram/wng.cpp`)

A C++ re-implementation of `CTL_NG_QSym` with the same history rule, the same exact far end, and the warm start as
an option. It agrees with busycoq on 40 random lemmas of `NG_v1.v` (all NONHALT with their own parameters) and on the
two same-table lemmas `nonhalt12951` and `nonhalt13144`.

```sh
g++ -O2 -std=c++17 -o wng wng.cpp
./wng 1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF 30000 3 12 2 0       # NONHALT 14630 configurations, 1928 symbols, 0.03 s
./wng 1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF 30000 3 12 2 0 -c    # cold: UNKNOWN (abstract halt)
./wng 1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF 0 3 12 2 0           # from blank: UNKNOWN
```

**Ablations on 1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF** (windows `NG_n` of 2, 3, 4, 6, 8; histories
(exact, compressed) of (12, 2), (8, 4), (6, 8), (16, 0), (12, 4), (1, 12), (0, 6), (4, 0)):

| start | histories | settings that close |
|---|---|---|
| blank tape (simT = 0) | all 8 | 0 of 40 |
| plain machine run 30,000 or 10^6 steps, histories empty (busycoq's `NG`) | (12, 2) | 0 |
| warm start, no histories, windows 2 to 12 | none | 0 of 14 |
| warm start 30,000 or 10^6 steps | (12, 2), (8, 4), (16, 0), (12, 4) | all windows 2 to 8, except (12, 2) and (8, 4) at window 2 |
| warm start | (6, 8) | windows 3 to 6 |
| warm start | (1, 12), (0, 6), (4, 0) | none |

The other machine of cryptids pull request 42, 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE, does not close with any
of 75 settings (blank, 30,000 and 10^6-step starts; windows 2 to 8; the first five histories; limit 2 million
configurations): 49 derive a halt, 26 hit the limit.

So the closing ingredient is **at least about 8 exact visits per cell, started from a settled tape**. The window can
be as small as 2. The results at 30,000 and 10^6 steps are identical, configuration for configuration.

**When the warm start begins to work.** With (12, 2) and window 3, starts at 15,000 steps and earlier derive a halt;
16,423 steps and later close (bisection; 16,423 to 16,923 give slightly larger sets, from about 25,000 on the set is
always the same 14,630 configurations). Nothing visible happens at step 16,423 (the head is at cell -120 in state
D, in the left part of the tape); it is simply the first start whose cells no longer carry histories of the
growing phase that the abstraction can recombine into a halt.

## Why histories help this machine

The machine's tape is a frozen archive crossed by sweeps, plus a chaotic engine at the right end (the
[machine's README](../../1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF/README.md)). A cell's last 12 visits say which
sweeps crossed it in which states, which identifies its role: which position of the archive word
`1^5 0 1^6 0 1^4 0 1 0` it is, or which part of the engine. So three history symbols carry what a plain window of
dozens of bits would need, and a plain window cannot see far enough (no plain window up to 12 closes). This is the
same idea as naming a tail by the call that produced it ([`token-grammar.md`](token-grammar.md)): the history is a
label the machine writes on the tape itself. Here the label comes for free from the machine semantics, so no search
for classes is needed.

The warm start matters because the n-gram abstraction forgets order: any symbols that occur in the start
configuration, or are produced from it, can be glued together. From blank tape, the start includes the growing phase,
whose cells carry histories that never occur later; mixed with steady-state cells they give a path to the halt that
the real run cannot take. From a settled start these symbols are absent or few.

## How it compares

| | DeepMind (cryptids #42) | ours: `tokgram`, `fwnamed` | Alk (busycoq #121) |
|---|---|---|---|
| object | a grammar of 5 nonterminals over run lengths, 3 + 9 return shapes, written by hand (or by a model) | run tokens, tails named by the call that made them; exact 32-cell window at the regular end | 3-symbol windows of history-labelled cells |
| found by | hand / model | search, after a warm start of 10^5 steps (`fwnamed`) | existing busycoq search, after a warm start of 30,000 history steps |
| proof size | 1,693 lines of Lean | certificate checked by an independent Python checker, not a proof assistant | 58 lines of Rocq, one `vm_cast_no_check` |
| explains the machine | yes, fully | partly (the named tails) | no: the closed set is 14,630 opaque configurations |
| transfers | the method (grammar + return shapes) | screens of 501 holdouts: none | screen below |

The lesson for this repository: our NGramCPS tool (`tools/c/ngramcps.c`) has histories but only starts from
blank, and `fwnamed` warm-starts but has no histories. Neither combination was tried. In busycoq, a warm start costs
nothing to prove, so it is worth trying on every decider that takes a start configuration (CPS_LRU, RWL, CTL with
DFAs), not just `NG`.

## Same table, another start: open holdouts with a decided sibling

Alk's proof says that busycoq already decides this transition table started in states other than A. We searched
the 583 Rocq files of the BB6 branch (70a1ffc) for six-state tables equal to an open holdout's up to renaming states
and mirroring, with a start state that makes them a different machine (`../tools/warm-ngram/sametable.py`, full
output in `../tools/warm-ngram/sametable-501-nov28.txt`). Files named `Eq*` (equivalence statements) and halting
proofs are left out of this table; 16 holdouts have a sibling proved to halt (`RWLAccHalt*`).

| open holdouts (one line = one table) | sibling proved non-halting in |
|---|---|
| 1RB---_1LC0LC_1RD1LB_1LE1RD_0LA1LF_1LD0RF | `RWL_mod` |
| 1RB---_1RC0LD_0LB0RE_1LB1LC_1RD1RF_1RD1RA | `Ind` |
| 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD, 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE, 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC | `CTLv2` |
| 1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA | `CPS_LRU` |
| 1RB0LD_1RC0RB_1RD1RF_1LE0LD_1RB1LA_---0RE, 1RB0RA_1RC1RF_1LD0LC_1RA1LE_1RA0LC_---0RD, 1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC | `FAR` |
| 1RB0LE_0RC0RA_1LD0LC_1LA0LB_1RA1LF_---0LC | `NG` |
| 1RB0LE_0RC0RD_1LC0RB_0RE1RD_1LF1LE_0LA--- | `CS` |
| 1RB0LE_1LC0RA_1RD0RC_1LA0LD_1LB0LF_1LC---, 1RB0RF_1RC0LE_1LD0LC_1RE0RD_1LB0RA_1RC--- | `CTLv1` |
| 1RB0LF_1LC1RA_0RD1LB_0LA0RE_1RC1RB_---0LD | `FAR` |
| 1RB0RA_1LC0LE_1RA1LD_0LB1LF_1LD0RC_1LB---, 1RB0RE_1LC1RD_1LA0LC_0RA1RF_1RD0LB_1RA--- | `FAR` |
| 1RB0RE_0LC1LE_0RD1LD_1RA1LF_1LC0RA_0LB--- | `CPS_LRU` |
| 1RB0RE_1RC0RE_1LD1RB_1LA0LA_1RF0LC_---0RC | `RWL_mod` |
| 1RB1LA_1RC1RE_1RD0RD_1LA1RC_1RF0LE_1RA---, 1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA | `RWL_mod` |
| 1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA | `CPS_LRU`, `RWL_mod` |
| 1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE | `CubicCap` |
| 1RB1RF_0RC1RD_1LC1LA_0LE1RE_1RA0RB_---0LC | `CPS_LRU` |
| 1RB1RF_1LC0RB_1RD0LC_1LE1RA_0RC1LB_---1RE | `CTLv1` |

**The `NG` sibling.** 1RB0LE_0RC0RA_1LD0LC_1LA0LB_1RA1LF_---0LC has the table of `NG_v1.v` `nonhalt11435`
(1RB0RC_1LC0RE_0LD0LB_1RA0RD_1LB1RF_---0RD, window 16, histories (2, 6)). With those settings it derives a halt from
blank and from a 30,000-step start, and runs past 40 million configurations from a 100,000-step start
(97 s, still open). So it does not transfer directly; a sibling's certificate describes the sibling's run, which may
never visit the region where the holdout spends its time.

**The CPS_LRU and RWL_mod siblings.** The files `CTLv1.v` and `CTLv2.v` use the same two deciders, so 19 sibling
proofs, covering 20 of the 24 holdouts, use `CPS_LRU` or `RWL_mod`. Both are the generic CTL search on the block
machine (blocks of `bsz` cells, each block crossed in at most `bmaxT` steps), with a different automaton on each
side: `CPS_LRU` keeps the `len3` blocks at the far end exactly plus a least-recently-used list of the blocks near the
head; `RWL_mod` keeps runs of equal blocks with counts capped at `mnc` and counted modulo `mod`. Both already take a
start time `simT` (the siblings use 1,001; one uses 10^8) and start from the plain machine, so no histories are
involved. `../tools/warm-ngram/wblk.cpp` re-implements both. It reproduces all 19 sibling proofs with their own
parameters (NONHALT, 570 to 91,629 configurations).

Run on the 27 (holdout, sibling) pairs with the sibling's parameters, from starts of 1,001, 10^4, 10^5, 10^6 and
10^7 steps (135 runs, limit 5 million configurations, `sibling-runs-nov28.txt`): **none closes.** 58 runs derive a
halt and 77 hit the limit of configurations or symbols. The siblings' own closed sets have at most 92 thousand
configurations, so runs at 5 million are not near misses: the holdout's run covers far more of the abstraction than
the sibling's.

Still not tried: the `FAR` siblings (finite automata reduction, which checks the start configuration against a
closed regular language rather than searching from it; 6 holdouts), `CS`, `Ind` and `CubicCap` (hand-written or
templated proofs, one holdout each).

## Screen of the 501 open holdouts

The same 501 open holdouts as the frontier-window screen. 90 settings each: warm starts of 10^4, 10^5 and 10^6
steps; windows of 2, 3, 4, 6 and 8 symbols; histories (12, 2), (8, 4), (6, 8), (1, 12), (0, 6) and (4, 0), with
`LRU_n` = 0, at most 30,000 symbols and 1 million configurations per run (`../tools/warm-ngram/screen.py`, run as four
`longrun` jobs `warm-ngram-screen-501-s0` to `s3`, 2.2 hours on 4 cores). Every result is in
`../tools/warm-ngram/screen-501-nov28.tsv.gz`.

**No open holdout closes.** Of the 45,090 runs, 34,253 derive a halt and 10,837 stop at the limit; none timed out.
For 144 machines every one of the 90 runs derives a halt. With the same grid, the positive control
1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF closes in 20 of 90 settings (none at 10^4 steps, which is before its
threshold of 16,423).

| window | halt derived | limit |
|---|---|---|
| 2 | 7,897 | 1,121 |
| 3 | 7,428 | 1,590 |
| 4 | 7,092 | 1,926 |
| 6 | 6,304 | 2,714 |
| 8 | 5,532 | 3,486 |

The start time hardly matters for the holdouts (11,622, 11,349 and 11,282 halts derived at 10^4, 10^5 and 10^6
steps). As with the frontier-window screen, a run that stops at the limit is not a negative result, but a closure
the size of Alk's (15 thousand configurations) would have been found.

## What we take from it

1. **Machine-written labels beat learned ones when they work.** A cell's visit history is a class name the machine
   writes for free. Our call-named classes are the same idea, found by search. For machines whose roles are visible in
   how sweeps cross cells, histories are the cheap thing to try first.
2. **Start late, keep everything.** Any abstraction that closes over symbols forgets the order of the start tape. A
   warm start removes the transient's symbols from the closure, but only if the augmented tape is simulated; wiping
   the augmentation afterwards (busycoq's `NG`) gives the transient back. Our `ngramcps.c` should get a warm start
   with histories; `fwnamed` already warm-starts.
3. **In busycoq a warm start is free to prove.** The CTL search is proved sound for any start configuration, so any
   decider of `CTL.v` can be run after `DH_cconfig_steps` with no new lemma beyond the 20-line chain of
   `hist_decide_spec`. This is a cheap pattern for our own submissions.
4. **This machine was an easy case.** It is a translating archive whose middle freezes, so after a short transient its
   whole tape is a fixed set of history-labelled cells. The screen suggests most open holdouts do not have that
   property at these window sizes: either the abstraction derives a halt, or the closure grows past a million
   configurations.
