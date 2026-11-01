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

**Computed**: the closed-form map agrees with the run on all 1,205 passes it covers in the first 10¹⁰ steps, and the
full map `pass` (run by Lean, and its Python transcription `next_full`) on all 1,786 (`py/macro.py check-full`);
all 3,845 pass starts in the first 10¹¹ steps are good; a recursive pass from a good list breaks goodness only when
the last block is 3 or 6 (exhaustive on small lists, random on larger ones; `py/blocks.py`).

**Observed only**: the width grows like the square root of the step count; when the last block is a multiple of 3 the
converter carries on into further blocks, so the routes are an infinite family (`notes/LAB_NOTES.md`).

**Open**: that the head does not drift left without bound (with it, the recursive pass always finishes, `pre` always stops, and `c ≥ -1` for every list follows), whether a bad last block 3 or 6 is ever
reached, and the question itself.

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
| `lean/EdgeCert.lean` | the closed tape language (windows of three cells), generated by `bbtools.ctl.lean_file` |
| `lean/Edge.lean` | the left end, and halting only at the right edge, from the language checked by `decide +kernel` |
| `lean/Axioms.lean` | prints what each theorem rests on |
| `lean/check.sh` | compiles the shared library, then the files above |
| `py/blank.py` | the run from blank tape on the shared simulator: summary, records, D at the left end |
| `py/macro.py` | pass starts of the run, the pass maps (`next_pass`, and `next_full` mirroring `lean/Recur.lean`, `pre` mirroring `lean/Formula.lean`), and their comparison |
| `py/blocks.py` | which pass starts can lead to a halt: the run, exhaustive and random checks, recursive offsets |
| `tests/test_machine.py` | generated files current, the page current, C against Python, the facts in the notes |
| `status.json` | the source of the proof-status page (`tools/pages/build_status.py`) |

## Check

```sh
bash scripts/setup-lean.sh && . /etc/profile.d/lean.sh
bb6-1RB1RA_1LC1LD/lean/check.sh
python3 bb6-1RB1RA_1LC1LD/tests/test_machine.py
python3 tools/pages/build_status.py bb6-1RB1RA_1LC1LD/status.json pages/1RB1RA_1LC1LD/proof-status.html   # after editing status.json
```
