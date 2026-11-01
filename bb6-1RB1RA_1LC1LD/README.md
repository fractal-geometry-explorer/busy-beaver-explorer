# The six-state machine 1RB1RA_1LC1LD_1LD0LB_1RE0RF_---1RD_1RA1RB

Whether this machine halts from blank tape is open. This folder holds its work; the shared tools are in
[`../tools`](../tools), the proof-status page is [`../pages/1RB1RA_1LC1LD/proof-status.html`](../pages/1RB1RA_1LC1LD/proof-status.html)
(built from [`status.json`](status.json)), and the log is [`notes/LAB_NOTES.md`](notes/LAB_NOTES.md).

## What is established

**Proved in Lean, kernel only** (`lean/Blank.lean`): the machine halts exactly when it is in E on a 0, and
`D>0 0` halts on the next step (`step_none_iff`, `halt_shape`); the tape after 46 steps (`blank_at_46`); no halt in
the first 20,000 steps (`blank_runs_20000`).  In `lean/Edge.lean`: D with a 0 on its left, in particular at the
left end, has a 1 on its right, forced by the step that brings D there (`d_one_right`, `d_left_end`); a closed tape
language (`lean/EdgeCert.lean`, from `tools/py/bbtools/ctl.py`) covers the whole run from blank tape (`reach_inv`),
so past the head two 0s in a row occur only in the blank region (`right_no_double_zero`), `D>0 0` occurs only with
blank tape from D on (`d_zero_zero`), and the machine halts if and only if E reaches the blank region at the right
(`halt_at_edge`, `halts_iff_edge`).

**Proved in Lean with `native_decide`**: no halt in the first 10¹² steps (`blank_runs_1e12`, `lean/Count.lean`): the
pass map with step counts, run for 8,257 passes from `1^10 0 1^3`, reaches a pass start at step 1,000,110,302,407.
Only that evaluation trusts the compiler; each pass and its step count is kernel-checked (`passesC_sound`).  Also a
plain run of 10,000,000 steps (`blank_runs_10M`).

**Computed** (trusted C/Python, tested): no halt in the first 10¹¹ steps (`tools/c/tmrun.c`); no conserved
a·ones + b·pos + W[state] modulo 2 to 12 (`tools/py/bbtools/invariants.py`).

**Proved in Lean, kernel only** (`lean/Macro.lean`, on the rules of `lean/Rules.lean`): the run is a sequence of
passes, each starting with A on the blank cell right of blocks of ones; when the last block is not a multiple of 3 the
next pass start is given by `next` (`next_sound`, every block length, any tape further left); a last block 1 halts and
4 halts one pass later (`K_zero_halts`, `kA0`); the first four pass starts from blank tape (`blank_passes`).

**Proved in Lean, kernel only** (`lean/Blocks.lean`): call a pass start good if every block is at least 2 and the last
block is neither 1 nor 4; every covered pass, and every run of covered passes, keeps a pass start good (`next_good`,
`nextIter_good`), so from a good pass start a halt needs a recursive pass (last block a multiple of 3).

**Proved in Lean, kernel only** (`lean/Recur.lean`): when the last block is a multiple of 3 the pass is followed by a
machine on lists of numbers (`astep`: blocks to the left, words `0 1^k` to the right), each of whose steps is proved
sound (`astep_sound`); with `next` this gives the pass map `pass` for every last block, and whatever it returns, the next
pass start or a halt, the machine does (`pass_sound`, `passes_sound`; that it always finishes is not proved).  From
blank tape, 100 more passes by `pass`, evaluated by the kernel, reach `1^162 0 1^206 A>0` (`blank_passes_104`).
In `lean/Count.lean` the same map carries the exact number of machine steps of each pass (`passC`, `passesC_sound`).

**Proved in Lean, kernel only** (`lean/Finish.lean`): the cells from the head to the right end, read from the right
end, go down in dictionary order at every step of the block machine (`astep_key`), so it never repeats a
configuration; if its head stays within `N` cells of the right end and it meets no case it does not cover, it ends the
pass within `3^N` steps (`arun_finishes`, `pass_finishes`).  Whether the head can drift left without bound is open.
**Proved in Lean, kernel only** (`lean/Formula.lean`): a recursive pass from `…, x, 3j` ends in a loop over the words
`0 1 1` that adds 2 to the last block per word (`tail_end`); what comes before the loop never reads past the words in
front of it, so it is run once for all `j` (`pre`, `pre_sound`), and the next pass start has last block `2j + c` with `c`
depending only on the blocks to the left (`recur_sound`, every `j ≥ u`, `u ≤ 2`).  For `x = 2`, closed form for every
list to the left: `c = -1`, so a last block 3 after a 2 halts and a last block of 6 or more keeps a good pass start good
(`recur_two`, `recur_two_three_halts`, `recur_two_good`).  `c ≥ -1`, `-1` exactly for `x = 2`, on all 819 lists of 1 to
3 blocks of 2 to 10, every `j` (`recur_small`).
**Proved in Lean, kernel only** (`lean/Offset.lean`, `lean/OffsetData.lean`): for every list of blocks of at least 2 to
the left, of any length, if `pre` stops then `c ≥ -1`, and `c ≥ 0` unless `x = 2`; at most two words are taken (`u ≤ 2`),
and the blocks it leaves are at least 2 (`offset_bound`).  So for every `j ≥ 2` a good list with last block `3j` passes
to a list of blocks of at least 2 with last block at least `2j - 1` (`recur_next`).  The proof is an abstract
interpretation of the block machine (numbers up to 3 exact, larger ones by residue mod 3; three blocks and two words
explicit, the rest by its shape); the kernel checks the 4,463 reachable descriptions in 127 pieces.  It assumes that
`pre` stops.
**Proved in Lean, kernel only** (`lean/Stops.lean`): `pre` never gets stuck on a good list: at each of the 4,463
descriptions the block machine has a next step unless `pre` stops or takes a supply word there (`prog_ok`), and at most
two words are taken.  With the key of `Finish.lean` this gives: if every configuration of the run keeps at most `N`
cells (head offset plus the cells of the words), `pre` stops within `4 · 3^N` steps (`pre_stops`), so `recur_next`
holds with that bound in place of the assumption (`recur_next_bounded`).  The only thing left is the bound itself.
**Proved in Lean, kernel only** (`lean/Chain.lean`): `Good` is not kept by every pass: `2 2 3` and `3 6` are good and
halt (`two_two_three_halts`, `three_six_halts`).  Call a pass start safe if it is good, has at least two blocks, and has
a last block 3 only after a block of at least 6 (`Safe`; the run reaches `10 3`, `blank_safe`).  If `pre` stops, a safe
pass start with last block other than 3 and 6 is followed by a safe one (`safe_pass`; a covered pass makes a last block 3
only from 7, the block to its left gaining 6); a last block 6 after a 2 gives a last block 3 after a block of at least 10
(`six_after_two`); a last block 6 after any other block gives last block `4 + c`, `c ≥ 0`, which halts if `c = 0` and is
safe otherwise (`six_pass`).  So, given that `pre` stops, a halt from a safe start needs one of two open cases: **A**, a
last block 3 after a block of at least 6 not followed by a safe start (computed: never; `c` is 0 with two supply words,
or at least 3, `py/blocks.py chain`), or **B**, a reached last block 6 with `c = 0`, which does occur on good lists
(`8 6 → 2 11 4`) and so needs the history of the run.
**Proved in Lean, kernel only** (`lean/CaseB.lean`): case B needs that history.  `16 16` and `314 54` are safe, every
block even (as the leftmost block always is on the run), and halt by case B (`sixteen_halts`, `chain_54_halts`).  If
`pre` stops, a safe start with last block other than 3 and 6 passes to a safe one whose last block is at least two
thirds of the old one less 5/3, and is 6 only if the old one was 9, or 2 after a block 3 (`safe_pass_shrink`).  So a
halt by case B needs the last block to come down to 9 first, by at most 3/2 a pass.  No lower bound on the last
block by the size of the tape is kept by every pass (`lean/Bound.lean`, `no_total_bound`): a covered pass from a last
block 1 mod 3 shrinks it while every other block stays or grows.  On the run the descents get rarer fast enough that
the chances of reaching 9 sum to a finite number (heuristic, `py/blocks.py descents`, `notes/LAB_NOTES.md`).  Nor do residues
separate them: mod 27 the run's last two blocks take 728 of the 729 pairs, and every known halting start shares its
pair with the run mod 54 (`py/blocks.py residues`).
**Proved in Lean, kernel only** (`lean/Tokens.lean`): `pre` at A before the words `1, 2` starts a carry over the blocks
that are 1 mod 3 (`carry`), and how it ends when it stops at a block `3m + 3`, at a block `3m + 8`, or past the leftmost
block (`row_zero`, `row_two`, `row_end`), with the pairs `2 1`, `2 3`, `3 2` that write no words; counting words
other than 2 and nonzero blocks, the count goes up only at the rows that start a new block at the left end
(`row_zero_tokens`, `row_two_tokens`, `row_end_tokens`).  Computed: at most (starting count + 2) such growth steps.

**Computed**: the closed-form map agrees with the run on all 1,205 passes it covers in the first 10¹⁰ steps, and the
full map `pass` (run by Lean, and its Python transcription `next_full`) on all 1,786 (`py/macro.py check-full`);
all 3,845 pass starts in the first 10¹¹ steps are good; with the block left of the last other than 2, the offset is 0
exactly when `pre` takes two supply words, and on the run to 10¹² steps case B is never reached, offset 0 occurs at most
3 recursive passes in a row and the smallest last block from pass 2,000 on is 375 (`py/blocks.py caseb`); a recursive pass from a good list breaks goodness only when
the last block is 3 or 6 (exhaustive on small lists, random on larger ones; `py/blocks.py`).

**Observed only**: the width grows like the square root of the step count; when the last block is a multiple of 3 the
converter carries on into further blocks, so the routes are an infinite family (`notes/LAB_NOTES.md`).

**Open**: that the head does not drift left without bound (with it, the recursive pass always finishes, `pre` always stops, and `c ≥ -1` for every list follows); case A of `lean/Chain.lean`
(a last block 3 after a block of at least 6) and case B (whether a last block 6 with `c = 0` is ever reached); and the
question itself.

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean` | the machine, generated by `tools/py/bbtools/leangen.py` (namespace `BB6c`) |
| `lean/Blank.lean` | bounded runs from blank tape and the halting configurations |
| `lean/Rules.lean`, `lean/rules.py` | the rules of one pass, proved along symbolic runs (generated) |
| `lean/Macro.lean` | the pass map `next` on block lists and `next_sound` |
| `lean/Blocks.lean` | the covered passes keep every block at least 2 and the last block off 1 and 4 |
| `lean/Recur.lean` | the block machine for a last block that is a multiple of 3, and the pass map `pass` for every last block |
| `lean/Finish.lean` | the block machine never repeats a configuration, and finishes the pass when its head stays within a bound |
| `lean/Formula.lean` | the recursive pass ends with last block `2j + c`: the final loop, `pre` once for every `j`, `x = 2` in closed form |
| `lean/Offset.lean` | `c ≥ -1` for every list of blocks of at least 2, if `pre` stops: the abstract interpretation and its soundness |
| `lean/OffsetData.lean` | the 4,463 reachable abstract descriptions as a search tree, checked by `decide +kernel` piece by piece; generated by `lean/OffsetGen.lean` (`check.sh` checks it is current) |
| `lean/Stops.lean` | `pre` never gets stuck on a good list, so it stops when the cells stay bounded |
| `lean/Chain.lean` | good starts that halt, and the reduction of a halt to a last block 3 after a block of at least 6, or 6 with `c = 0` |
| `lean/CaseB.lean` | case B: safe even starts that halt by it, and how fast the last block can fall (only from 9 to 6) |
| `lean/Bound.lean` | no lower bound on the last block by the total is kept by every pass |
| `lean/Tokens.lean` | `pre` at its A states: the carry over blocks 1 mod 3, the three ways it stops, the pairs that write no words, and the token count at each |
| `lean/EdgeCert.lean` | the closed tape language (windows of three cells), generated by `bbtools.ctl.lean_file` |
| `lean/Edge.lean` | the left end, and halting only at the right edge, from the language checked by `decide +kernel` |
| `lean/Axioms.lean` | prints what each theorem rests on |
| `lean/check.sh` | compiles the shared library, then the files above |
| `py/blank.py` | the run from blank tape on the shared simulator: summary, records, D at the left end |
| `py/macro.py` | pass starts of the run, the pass maps (`next_pass`, and `next_full` mirroring `lean/Recur.lean`, `pre` mirroring `lean/Formula.lean`), and their comparison |
| `py/blocks.py` | which pass starts can lead to a halt: the run, exhaustive and random checks, recursive offsets, case A of `lean/Chain.lean`, case B (`caseb`), descents of the last block (`descents`), their residues (`residues`) |
| `py/blocks.py` | which pass starts can lead to a halt: the run, exhaustive and random checks, recursive offsets, case A of `lean/Chain.lean` |
| `py/tokens.py` | `pre` at its A states: two words eaten each time, the token count, growth steps (`notes/LAB_NOTES.md`, 1 November, ranking function) |
| `tests/test_machine.py` | generated files current, the page current, C against Python, the facts in the notes |
| `status.json` | the source of the proof-status page (`tools/pages/build_status.py`) |

## Check

```sh
bash scripts/setup-lean.sh && . /etc/profile.d/lean.sh
bb6-1RB1RA_1LC1LD/lean/check.sh
python3 bb6-1RB1RA_1LC1LD/tests/test_machine.py
python3 tools/pages/build_status.py bb6-1RB1RA_1LC1LD/status.json pages/1RB1RA_1LC1LD/proof-status.html   # after editing status.json
```
