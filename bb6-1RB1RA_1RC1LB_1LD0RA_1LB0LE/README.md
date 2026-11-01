# The six-state machine 1RB1RA_1RC1LB_1LD0RA_1LB0LE_1LF1LD_---0LD

Whether this machine halts from blank tape is open. This folder holds its work; the shared tools are in
[`../tools`](../tools), the proof-status page is
[`../pages/1RB1RA_1RC1LB_1LD0RA_1LB0LE/proof-status.html`](../pages/1RB1RA_1RC1LB_1LD0RA_1LB0LE/proof-status.html)
(built from [`status.json`](status.json)), the explainer
[`../pages/1RB1RA_1RC1LB_1LD0RA_1LB0LE/explainer.html`](../pages/1RB1RA_1RC1LB_1LD0RA_1LB0LE/explainer.html) runs the
machine, its passes and the closed form in the browser, and the log is [`notes/LAB_NOTES.md`](notes/LAB_NOTES.md).

Not to be confused with [`../bb6-1RB1RA_1RC1LB`](../bb6-1RB1RA_1RC1LB), the machine
`1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB`: the two share their first three states, so this folder is named by four.

## What is established

**Proved in Lean, kernel only**: the machine halts exactly in F on a 0, and `0 E>0` halts on the next step
(`step_none_iff`, `halt_shape`); the first pass start `1^2 0 1^2 A>0` at step 17 (`blank_at_17`); no halt in the
first 20,000 steps (`blank_runs_20000`), all in `lean/Blank.lean`. The pieces of a pass for every length
(`lean/Rules.lean`): `start`, `de_sweep`, `de_sweep_odd`, `e_cross`, `d_stop`, `zig`, `a_sweep`, `b_sweep`, `d_stop_empty`,
`zig_empty`, `turn`. The closed form of a pass for every block list (`lean/Pass.lean`: the map `next`, the machine
follows it, `pass`, and halts where it says so, `pass_halt`), a pass adds 4 ones (`next_sum`), a halting pass has an
odd count (`next_halt_odd`), and so **the reduction**: if the machine halts from blank tape, the orbit of `next` reaches
a pass whose sweep stops at a block of a single 1 (`halts_only_by_one`). Narrowed (`lean/Front.lean`): every block after the first stays at least 2
(`next_good`), so that stop can only be at the first block, after the sweep crosses all the others (`one_front`); with
4 | ones two passes in a row never both stop at the first block (`front_twice`); so if the machine halts, some pass
start is `1 0 1^e 0 … 0 1^b A>0` with every `e` even and `b` odd, and the pass before did not stop at its first block
(`halts_only_at_front`).

**Proved in Lean, kernel only: the return map below 2^62** (`lean/Return.lean`, `lean/Return62.lean`). Every
two-block state `[a, 2a+d]`, |d| ≤ 3, a ≥ 5, reaches one with d = 1 in at most three passes (`chain_0` … `chain_m3`,
for every a). For every a = 1 mod 4 with 5 ≤ a < 2^62 the pass map takes `[a, 2a+1]` to `[a+12k, 2(a+12k)+1]` in
exactly 9k passes (`returns_2_62_kernel`): `snext` is the pass map on residue classes p + q·u, proved to agree with
`next` at every u (`snext_ok`), and `explore` (proved sound, `explore_ok`) runs the classes, splits them by parity,
and runs single values concretely where a class is not uniform. With `orbit_ok_upto` (if every a below B returns,
the first (3B+4)/4 passes are block lists) and the reduction: **the first 3·2^60 + 1 ≈ 3.46·10¹⁸ passes never stop at a
block of 1, and the machine reaches each of their pass starts** (`no_one_3e18_kernel`; pass n has 4n ones, pass 4
is `[5, 11]`). One `decide` on the whole class needs more memory than a machine has, so `lean/return62.py` cuts it
into 1,575 subclasses checked by `decide +kernel` one theorem each (`lean/R62/`, 8 files) and joined by `Cov.split`;
about an hour of CPU, 17 minutes on 4 cores (`lean/check_return62.sh`, its own CI workflow). The regular check has the kernel for a < 2^16
(`returns_2_16`).

**Proved in Lean with `native_decide`**: no halt in the first 10,000,000 steps (`blank_runs_10M`); the return map
below 2^62 in one evaluation of `explore` (`returns_2_62`, `no_one_3e18`, seconds), the same statement as above.

**Computed** (trusted C/Python, tested): no halt in the first 10¹¹ steps (`tools/c/tmrun.c`); the closed form of the
pass map (`py/passmap.py`) gives every pass start of the first 10⁹ steps (1,005 passes), and Lean's `next` agrees with it
on 3,000 random lists and the first 400 passes; no conserved a·ones + b·pos + W[state] modulo 2 to 12. **The return
map** (`py/returnmap.py`, the computation the Lean one follows, on the pass map that `pass` proves): run on
residue classes of a down to mod 2^74, no excursion halts or meets a stop block of 1 for 5 ≤ a < 2^74, so with
`halts_only_by_one`, **no halt in the first 1.4·10²² passes** (resting on the Lean pass map and on this Python
computation, whose `passmap` is tested against Lean's `next`); down to mod 2^62 it gives the 19,231 routes, k = 1
to 11, of the Lean theorem above.

**Computed, by plain iteration** (`c/passorbit.c`, the closed form in C, checked against `py/passmap.py`; resting on
the Lean pass map): the first 10¹¹ passes from `[2, 2]` one by one, with no residue classes, never meet a stop block
of 1, an independent check of the start of the return-map result; after pass 50 no sweep stops at a block below 59 or
below 1.4% of the ones.

**Searched** (heuristic for the general question; `notes/LAB_NOTES.md`, 31 October): which starts meet a stop block
of 1. Of all 268 million lists of up to 28 ones, every one with an odd count meets it or halts, and every event comes
by pass 59; every two-block start `[a, b]` with a ≥ 2, a, b ≤ 10⁴ and 4 | a + b runs 1,000 passes without it; random
lists with large blocks never meet it. The event needs a sweep to stop at a block of 3 in the first two places one pass
before (`[x, 3, z]`, x ≡ 2, z ≡ 3 mod 4, meets it on its second pass and then halts on the machine).


**The first block** (`py/front.py`, trusted Python on the Lean pass map): along the first 10⁸ passes the first block never
falls by more than a factor 32 before it grows again (at most 5 halvings in one descent), and after pass 50 it stays
above 0.7% of the ones, while a stop block of 1 needs it to fall to 1. No invariant of block sizes or of residues
modulo a fixed power of 2 can exclude the event (`notes/LAB_NOTES.md`, 31 October: small starts reach it by a halving
loop of the first block, and what keeps the orbit out of it is the 2-adic digits).

**A second invariant, psi** (`py/invsearch.py`, `notes/LAB_NOTES.md`, 1 November): psi = y_k − 2y_(k−1) + 4y_(k−2) − …
obeys 2·psi(next) = −psi + 3(−2)^n − 7 exactly, n the blocks the sweep crosses past the last (a polynomial identity
checked by sympy for k ≤ 12; the Lean thread has it as `psi_next`). On `[a, 2a+d]` it is d; it ends the halving loop
above within about log₄|psi| rounds; on the orbit (10⁸ passes, computed) and on every excursion class to mod 2^66 it
stays in −21..24 with at most 6 blocks. **Conditional reduction**: with at most 6 blocks, psi, `front_twice` and a
finite graph give at most 9 front stops between other changes of the first block, so a first block of 1 needs one of
those changes to leave it at most 511 (exact). A game on that graph keeps it above about 10⁻⁵ of the ones (numeric,
not certified). **But the block count is not bounded by 6 on excursions** (`lean/Seven.lean`, kernel): from
`[a, 2a+1]` with a = 2^203 + 2^221 + 1 (a = 5 mod 12) the machine reaches a pass start with 7 blocks after 204
passes, then returns normally after 216. The classes to mod 2^66 missed it because it needs a mod 2^222. Whether the
blank orbit meets such an a is not proved (expected, near pass 2^220; heuristic), and whether any fixed bound holds is
open; the nesting of sentinel orbits suggests not (`notes/LAB_NOTES.md`, 1 November).

**Observed only**: on every route down to mod 2^74 the stop blocks stay above about a/64, shrinking like 2^(−m/10) or slower
with the depth m of the class. The route list is infinite (the tail of the first pass lives v₂(a−1) passes), finite
for each k.

**The return map's dynamics** (`py/dynamics.py`, `notes/LAB_NOTES.md`, 31 October): G is a counter (a' = a + 12k,
k ≥ 1, by `next_sum`), and its orbit runs through 95% of all a = 5 mod 12 in order, so what matters is whether
*every* excursion is safe, not where one orbit goes (computed). An excursion reads a few low bits of a. The a not yet
covered form a 2-adic set of dimension about 0.19, and on it the bits of a mix as in Collatz, so the coefficients never
repeat (computed). Every route keeps a margin of a/64 against the 1/a a halt needs (heuristic). Verdict: not
Collatz-like at the level of G. A proof needs an inequality by induction, not a finite table.

**Open**: an induction for the excursion from `[a, 2a+1]` over the tail length, for a ≥ 2^62 (whether a sweep ever stops at a block
of 1), and so the question itself.

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean` | the machine, generated by `tools/py/bbtools/leangen.py` (namespace `BB6d`) |
| `lean/Rules.lean` | the pieces of a pass, generated by `lean/rules.py` with `tools/py/bbtools/symtm.py` |
| `lean/Blank.lean` | bounded runs from blank tape and the halting configurations |
| `lean/Pass.lean` | the pass map in closed form, proved for every block list, and the reduction to a stop block of 1 |
| `lean/Front.lean` | blocks after the first stay at least 2, no two front stops in a row, and the narrowed reduction |
| `lean/Seven.lean` | an excursion with 7 blocks: `run`, `run_reach`, `seven_blocks` |
| `lean/Return.lean` | the return map: the pass map on residue classes (`snext`, sound), `explore`, the short chains, the orbit up to a bound |
| `lean/Plan.lean`, `lean/return62.py` | the cut of the class a = 5 + 4u into pieces for the kernel; writes `lean/R62/` and `lean/Return62.lean` |
| `lean/R62/Shard*.lean`, `lean/Return62.lean` | generated: the pieces, each by `decide +kernel`, and the theorem below 2^62 |
| `lean/check_return62.sh` | checks the pieces in parallel (`JOBS`), then `Return62.lean`, and that it rests on no `native_decide` |
| `lean/Axioms.lean` | prints what each theorem rests on |
| `lean/check.sh` | compiles the shared library, then the files above |
| `py/passmap.py` | the pass map: closed form, a pass run on the machine, the orbit, statistics, a random check |
| `py/returnmap.py` | the return map on two-block states: the short chains, G(a), the run on residue classes |
| `py/front.py` | the first block along the orbit: descents, the halving loop |
| `tests/test_front.py` | the statements of `lean/Front.lean` on the Python closed form, and the orbit measurements |
| `py/dynamics.py` | the long-run dynamics of G: the orbit as a counter, the bits an excursion reads, the class tree and its open set, the mixing |
| `tests/test_dynamics.py` | the counter, the bits read, the tree to mod 2^26, the mixing at depth 32 |
| `tests/test_returnmap.py` | the chains, the classes down to mod 2^38, the classes against concrete runs, the orbit chain |
| `py/blockcount.py` | the 7-block witness, the sentinel orbit's block counts, the scan of a = 2^r + 1 |
| `tests/test_blockcount.py` | the witness, its (k, psi) route, the sentinel orbit at pass 203, the scan |
| `py/explainer_status.py` | writes the explainer's status panel from `status.json` |
| `tests/test_explainer.py` | the explainer's engine against `py/passmap.py` and the reference simulator; its status panel current |
| `c/passorbit.c` | the closed form in C: the blank orbit with checkpoints (`orbit`), and searches over starts (`comps`, `grid`, `random`) split into parts for `tools/c/run_parts.sh` |
| `py/passorbit.py` | checks `passorbit` against `passmap` (checkpoints and hashes, counts), and runs the machine after the event (`after`) |
| `runs/` | outputs of the long runs (`runs/README.md`) |
| `tests/test_passorbit.py` | `passorbit` against `passmap` and the machine, and the two-pass family |
| `tests/test_machine.py` | generated files current, the page current, C against Python, the closed form against the machine and the C run |
| `status.json` | the source of the proof-status page (`tools/pages/build_status.py`) |

## Check

```sh
bash scripts/setup-lean.sh && . /etc/profile.d/lean.sh
bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/lean/check.sh
JOBS=4 bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/lean/check_return62.sh                                        # 17 min on 4 cores
python3 bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/tests/test_machine.py
python3 bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/tests/test_passorbit.py
gcc -O3 -o passorbit bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/c/passorbit.c && ./passorbit orbit 100000000000   # about 35 min
python3 bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/py/passmap.py stats 2000000
python3 bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/tests/test_returnmap.py
python3 bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/tests/test_front.py
python3 bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/tests/test_blockcount.py
python3 bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/py/front.py stats 100000000   # about 4 min
python3 bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/py/returnmap.py classes 60    # 24 s (classes 72: 2.5 min)
python3 bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/tests/test_dynamics.py
python3 bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/py/dynamics.py orbit 300000; python3 bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/py/dynamics.py tree 72   # 4 min
python3 tools/pages/build_status.py bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/status.json pages/1RB1RA_1RC1LB_1LD0RA_1LB0LE/proof-status.html   # after editing status.json
python3 bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/py/explainer_status.py                                                                       # the same, for the explainer
python3 bb6-1RB1RA_1RC1LB_1LD0RA_1LB0LE/tests/test_explainer.py
```
