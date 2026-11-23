# Coq: a halting proof that waits for a halt, and the engine run

This folder turns busycoq pull request 93 (the DeepMind-style proof that `1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---`
halts) into a proof for this machine that is complete except for one computation: the run of the accelerated engine
until it stops. The engine has not stopped. Everything here was first set up in the t4-variants thread
(`holdouts/recent-proofs/followup/t4-variants.md`); this folder keeps the scripts and the 20 November 2026 runs.

## The reduction

Up to swapping E and F, this machine is the table

    U  = 1RB1RA_1LC0RD_1LD1LB_1LF0LE_0LB0LE_0RA---     (started in A)

and PR 93 works on

    T3 = 1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB---     (PR 93 starts it in C).

U is T3 with two changes. F is merged into E (T3's E1 `0LF` and F0 `0LB` are the moves of U's E1 `0LE` and E0 `0LB`), so
T3's halting transition F1 becomes "keep erasing to the left". And T3's D0 `1RA` becomes the detour D0 `1LF`, F0 `0RA`,
A1 `1RA`, which ends where `1RA` ends, unless the cell left of D holds a 1: then F reads 1 and U halts. So U halts
exactly when D reads 0 with a 1 on its left (`lean/Halt.lean` proves the same for the machine itself: a halt needs B
reading 0 with 0, 0, 1 to its left).

`mkU.py` rewrites PR 93's file for this machine: the engine runs on W = T3 with F1 := 0LF (no halting transition),
`HaltsU c` (U halts from the image of c) replaces `halts src_tm`, the raw step returns `None` on D reading 0 with a 1
on its left (lemma `haltsU_D0`), `det_step` carries each W step to U, and `perm_U` / `haltsU_iso` carry U to this
machine. None of PR 93's macro rules uses F1, so they hold for W unchanged, and none of its 34 base rules contains a D0
step with a 1 or an unknown cell on its left (t4-variants, `sim/rules.py`), so the engine sees every possible halt in a
raw step. With `run_ok` admitted the file compiles (Coq 8.20.1) and `Print Assumptions halt` lists only `run_ok`.

If the engine ever stopped at fast step N, `python3 mkU.py PR93.v U_A.v 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF A K`
with 2^K > N would be the complete proof (only the `vm_compute` of `run_ok` left to run).

## The run (20 November 2026)

The engine is the proof file's own definitions, extracted to OCaml (`build.sh`), so a stop of the extracted run is
exactly what `run_ok` would compute. Started in A, it passed fast step 18,449,229 without stopping (resumed from the t4-variants checkpoint at fast step 10,642,446). Every fast step is a
valid stretch of U's run (proved in Coq: `stepFast_spec`, `det_step`), and the tape it holds then has more than
2^4439 cells, each visited at least once, so **the machine does not halt in its first 2^4439 > 10^1336 steps**. This
rests on extracted code and OCaml, not on Coq's kernel.

### Where a halt could happen

A halt can only happen in a raw step, when the engine has left its macro rules. `ev3` records every entry into raw mode
by state, direction and the 8 nearest cells on each side; `ev2` prints every raw step where C or D reads 0 or F reads 1.
Through fast step 18,449,229 from blank tape (fast steps 0 to 11,000,000 and 12,251,076 onwards classified by `ev3`; the stretch between, and 5,000,000 to 5,400,000, checked by `ev2` for C0, D0 and F1):

| entry into raw mode | kinds (8 cells each side) | what follows |
|---|---|---|
| B or C at fast steps 4 and 6, on blank tape | 2 | the start; the only raw D0 moving left (step 7) has 0s on its left |
| B moving right, cells `1101 01..` to its left | 4 | B1, then D reads to its right with the 0 B wrote behind it: cannot halt (`enter_D`) |
| D moving right | 8 | the same: D was entered by B1, the cell behind it is 0 |
| C moving left reading 0, with `1 1 1` on its left | 2 | T3's halt: D, E, E erase three 1s, then the macro rules resume |

The last row recurred 10 times, at fast steps 4,449, 472,186, 1,067,749, 2,395,439, 4,340,637, 4,552,243, 4,970,192,
9,751,547, 10,647,772 and 10,969,745 (tape about 2^41 cells at the first and 2^3544 at the last), and not again up to
18,449,229. The two kinds in that row differ only in the 8th cell to the right, which the excursion never reads; the
11-step excursion is the same every time (checked at the first two with `pk2`).

The halting route is C reading 0 (moving left) and then D reading 0 with a 1 behind it. After the first 7 steps, every
raw C0 in the run met `1 1 1` on its left: D reads 1 and E, F erase leftwards. That is exactly T3's halting event, the
F1 at which PR 93's run stops. In U it is the same nearest cells every time (`0 1 1 1 0 1 1 0 1`, of which the excursion reads six), U erases three
1s, steps back and returns to the macro rules, and the event recurs once per lap of the counter. U's answer to it never
depends on anything beyond those cells, so the sibling's halting point gives no halting point for U: U survives each
lap the way it survived the first.

## The fast engine (22 November 2026)

Almost all of the extracted engine's time went into Coq's binary numbers: in the extracted OCaml a number is a list of
bits, and at 2^6000 cells every addition walks thousands of list cells. `ExtT4CZ.v` extracts the same definitions
(`T4C.v` as built by `build.sh`, nothing changed) with `positive`, `N` and `Z` realized by Zarith's integers: Coq's
standard `ExtrOcamlZBigInt`, plus `N.eqb`, `N.leb`, `N.ltb`, `Pos.eqb`, `N.double`, `N.succ_double` and `N.div2` written
as the Zarith functions with the same meaning. This is a change of number representation in the extracted code only;
`run_ok` in Coq is untouched. `buildz.sh OUTDIR` (after `build.sh`) builds `runz` and `zdigest` from it, and `cksdigest`
for the old engine.

- **Same states (computed).** `zdigest S N` prints an MD5 of the whole compressed state (every run, word, counter and
  digit list, with numbers in decimal) at fast step N, and `cksdigest CK` prints the same digest of a checkpoint of the
  old engine (`run.ml`). They agree at fast steps 10^3, 10^4, 10^5, 3·10^5 and 10^6 from start B, at fast step
  35,227,304 from start B (`fa3c4a9a98e3015d560c6619c6275d80`) and at fast step 29,077,778 from start D
  (`584e46fced19ef4fef6aec291f47d321`), the last checkpoints of the old runs. The new engine reaches those two points in
  under 3 minutes; the old one took several hours.
- **Speed.** About 27 times faster at 10^6 fast steps and far more on larger tapes: in one hour each of the three runs below
  went from blank tape to about 3·10^8 fast steps and 2^17800 cells; after 3.7 hours
  (stopped at 00:11 UTC on 23 November) they were at 6.0-6.6·10^8 fast steps and 2^25750 cells, growing by about
  2,000 bits of tape per hour. The checkpoints are kept outside the repository (about 37 MB each).
- `runz START MAXFAST CHECKPOINT` runs from blank tape (or resumes), saves every 3 minutes, and classifies every entry
  into raw mode like `ev3` (state, direction, 8 cells on each side), printing a kind when it is first seen.

| start | machine | fast steps, no stop | tape then | so no halt in the first | kinds of raw entry |
|---|---|---|---|---|---|
| A | 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF | 601,531,739 | > 2^25798 cells | 10^7765 steps | 21 |
| B | 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF | 627,839,771 | > 2^25751 cells | 10^7751 steps | 23 |
| D | 1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF | 659,729,468 | > 2^25808 cells | 10^7768 steps | 24 |

The new kinds of raw entry (more of the 8 neighbouring cells, the same situations) are all in the classes of the table
above: D moving right with a 0 on its left, D moving left onto a 1, B moving right, and C reading 0 moving left with
`1 1 1` on its left, the sibling's halting event. That event came 111 times from start A (97 from B, 105 from D)
and was survived every time. Every raw step is checked for the halt by the engine itself.

## Files

- `mkU.py PR93.v OUT.v MACHINE START K [fast]`: the proof for this machine (`... A K`); `fast` admits `run_ok`.
- `build.sh PR93.v OUTDIR`: the proof (with `run_ok` admitted), then the engine extracted from it, and the tools.
- `extra.v`, `ExtT4C.v`: printing helpers added to the engine module, and the extraction command.
- `run.ml`: `run A MAXFAST [CHECKPOINT]`, saves an OCaml Marshal checkpoint every 10 minutes and resumes from it.
- `ev2.ml`: `ev2 A MAXFAST [CHECKPOINT|none] [SAVE]`, the same with every raw C0, D0 and F1 printed with its context.
- `ev3.ml`: `ev3 A MAXFAST`, every entry into raw mode, classified.
- `pk2.ml`: `pk2 A FROM TO`, the compressed configuration at each fast step in a range.
- `ExtT4CZ.v`, `buildz.sh`, `runz.ml`, `zdigest.ml`, `sdigest.ml`, `cksdigest.ml`: the fast engine (Zarith numbers),
  its runner and the state digests that compare it with the plain engine (section above).
- `validateU.ml`: `validateU START MAXFAST MAXDIRECT`, the engine next to direct simulation of U (engine state F is U's E).
- Other starts of the same table (22 November 2026): `START=B M=1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA0RF build.sh ...`
  and `START=D M=1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD0RF build.sh ...` (wrappers in those machines' `coq/` folders,
  with their runs); `mkU.py` has a branch for each of the four machines.

PR 93's file: `verify/M_1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RDHHH.v`, sha256
`63964df1e1da61d8d3497a0faa03ad1ffe0bf0a331dcd9da7f3957fea4930c78`, on busycoq's BB6 branch at 33209bc. Run the tools
with `ulimit -s unlimited`.
