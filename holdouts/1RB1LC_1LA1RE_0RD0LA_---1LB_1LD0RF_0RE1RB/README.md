# 1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB

bbchallenge id 56057. One of the six-state holdouts whose halting from blank tape is open. Family: **binary counter moving a marker through a word**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LC |
| B | 1LA | 1RE |
| C | 0RD | 0LA |
| D | --- | 1LB |
| E | 1LD | 0RF |
| F | 0RE | 1RB |

## What it does

Each time the head, in state C, is at the left end reading `0 1 0` (an **overflow event**), the tape from the head on
is `C>0 (1 0)^z W` with W a word of odd blocks of 1s separated by single 0s. Read in pairs of cells (`1 0` = digit 0,
`1 1` = digit 1) the tape is a string of binary digits, and `(1 0)^z` is a run of z zero digits.

**Two counters on one clock.** Between two events the head shuttles around a point near the left end of W. Each
shuttle (a *tick*) adds one to a binary counter L on its left (the z digits of the prefix, written in pairs of cells
`0 0` / `1 1`, least significant digit next to W) and one to a binary counter R inside W (its least significant bit
next to the shuttle point): the turning points of the head left of the point follow the ruler sequence of L and those
right of it the ruler sequence of R. An event is an overflow of L: L has counted 2^z ticks, it is reset and gets one
more digit (z -> z + 1).

**The overflow law.** So at each event R has gained exactly 2^z. In W the bits of R sit at fixed digit positions
(slots), mostly 3 digits apart (`11b`, b the bit), with a few separating stretches between them. Running one event
again with every z from 0 to 16 (`py/overflows.py slots`) shows it directly: the next event has W changed by exactly
one binary carry that starts at slot z (digits p1 < ... < pk, 1 -> 0 at all but the last, 0 -> 1 at the last). In the
run, 55 of the 106 pairs of consecutive events up to 2·10^9 steps are such carries (`py/overflows.py check`); the
others are the restructures and the carries through the separating stretches just after them, which also rewrite
some separator digits.

**The marker.** Late in an epoch only the top bits move: W = P `111110` (`110`)^b `111`, where `110` is a 0 bit,
`111110` is the single 1 bit of the high part (the **marker**, cells `1^11 0`) and `111` is the end. Each event moves
the marker one block right (b -> b − 1), and the gap between events obeys **D' = 2D + 2** exactly (all 23 pairs of
consecutive marker moves in the first 5·10^10 steps).

**Restructures.** When R overflows (the marker meets the end) the word is rebuilt and z starts again. Started from one
event with different z, the restructure comes after the same number of steps for every z large enough, so it is
triggered by R, not by L; what it writes depends on z (L's digits are copied into the new word). In the first 10^11
steps the last three restructures came at steps 17,682,600 (102 digits), 5,745,422,543 (131) and 49,800,461,566
(163). At step 96,162,430,390 the run is at z = 30 with 192 digits.

**The accelerated run.** At a *tick start* the head, in A, reads 0 at the shuttle's base cell and turns right onto a
1. From one tick start to the next only the digits of L (cell pairs left of the base) and of R (single cells right
of it, with dead stretches between them) change, each by one binary increment, and the tick costs G(k) steps left of
the base plus F(j) steps at or right of it, k and j the carry lengths. `py/accel.py` learns the digit positions and the
two cost tables from directly simulated ticks, applies runs of ticks whose carries stay inside the known digits
arithmetically, and simulates everything else (new digits, overflows of either counter, rebuilds) cell by cell; every
directly simulated tick is checked against the cost tables. It gives exactly the events of the direct run to 2·10^10
steps (`py/test_accel.py`), and in 85 seconds reaches 1.6·10^45 steps: 842 events, 23 rebuilds (the last at
1.47·10^42 steps), W grown to 782 digits, 8,416 cost checks with no mismatch, and no halt.

**The right end.** The machine halts only in D on a 0. D is entered by C0 = 0RD, onto the cell A1 = 1LC has just
written (C is entered only by A1), so on a 1, and by E0 = 1LD, back onto the cell E came from; that cell is a 0 only
if E came by F0 = 0RE. So the machine halts exactly when F reads two 0s in a row, `F>0 0`. Inside the word W blocks
are separated by single 0s, so on the right sweep this happens at the end of the tape: the sweep must reach blank
tape in state F. On a block of 1s the sweep cycles E -> F -> B -> E (E1 =
0RF, F1 = 1RB, B1 = 1RE), so a sweep entering the last block in E halts at the end of the tape exactly when the block
has length 1 mod 3 (`lean/Edge.lean`, `lean/EdgeHalt.lean`). In the accelerated run to 1.6·10^45 steps the head reaches
blank tape at the right 83 times, always in E (24) or B (59), never in F; each epoch does it three times, in E and
then B at the first overflow of R and in B at the rebuild, with the end of the tape `...011011011011`,
`...110110110101` and `...101101101101`.

The machine halts only in state D reading a 0. From configurations of the same shape with random short words it often
halts within a hundred steps (`D>0 1` at the right end), so non-halting depends on the words the run writes.

## Status

Open. Proved in Lean (kernel): the halting configurations, no halt in 10,000 steps, and the right sweep through the
last block (halt at the end of the tape exactly for length 1 mod 3 when entered in E); with `native_decide`: no halt
in 10^7 steps, and, from a certificate accepted by a checker whose soundness is kernel-checked, **no halt in
1.2·10^70 steps** (`lean/Long.lean`). Computed (trusted C and Python): no halt in 10^11 steps; the overflow events and
their carry law as above; the accelerated simulator agrees exactly with the direct run to 2·10^10 steps. Not proved:
any of the counter laws for all parameters and all words (the certificate checks each tick shape only for the layouts
the run actually meets), and the question.

## How far it was run

Proved in Lean (`lean/Long.lean`, `native_decide`): 12,198,487,909,209,082,368,679,859,826,732,096,416,911,140,917,107,868,
420,374,132,270,946,987 ≈ 1.2·10^70 steps without a halt. Accelerated (`py/accel.py run 1e70`): to 1.2·10^70 steps
in 9 minutes, 20,226 batches, no halt. Direct C simulation to 10^11 steps
(z = 30, the fourth recorded epoch). With the marker law (`py/overflows.py
predict` on the events of an epoch whose marker is in the periodic tail) the end of an epoch can be placed exactly
from its last two events, since each further event is one doubling (D' = 2D + 2); the restructure itself is not
predicted, so the macro run stops at the end of the current epoch.

## What is established

**Proved in Lean, kernel only** (`lean/Blank.lean`): the halting configurations (`step_none_iff`); no halt in 10,000
steps (`blank_runs_kernel`).

**Proved in Lean, kernel only** (`lean/Edge.lean`, generated by `py/gen_edge.py` with `bbtools.symtm`, and
`lean/EdgeHalt.lean`): `sweep`, E> `(111)^n` -> `(011)^n` E> for any tape; `edge_stops`, a last block `1^(3n+1)`
entered in E ends in D on a 0, which halts; `edge_B_runs` and `edge_E_runs`, lengths 3n + 2 and 3n + 3 turn back in A
or D on a 1.

**Proved in Lean with `native_decide`**: no halt in 10^7 steps (`blank_runs_native`).

**Proved in Lean, kernel only** (`lean/Tick.lean`, generic over the machine, and `lean/Cert.lean`): the certificate
checker is sound, `checkCert_sound`: if `checkCert s = some N` then `steps N init = some c` for some `c`. See *The
certificate* below.

**Proved in Lean with `native_decide`** (`lean/Long.lean`): the certificate `lean/cert.txt` (770 KB, 60,256
operations, made by `py/accel.py cert 1e70`) is accepted, `cert_ok`; so `runs_N`, a run of N ≈ 1.2·10^70 steps from
blank tape; `no_halt_within`, every run of at most N steps is defined; `halt_late`, a halt, if any, comes after more
than N steps. The evaluation trusts Lean's compiler (`check.sh` compiles the checker to a shared library with the
toolchain's C compiler and loads it, about 4 minutes); the axioms are the usual three and the `native_decide` one.

**Computed** (trusted C): no halt in 10^11 steps (`tools/c/tmrun.c`; 385 cells, 312 ones). All 144 overflow moments
of the run have the shape `(1 0)^z W` with W of odd blocks; z rises by one between them except at 16 restructures.

**Computed** (Python, `py/overflows.py`): the carry law at 55 of the 106 event pairs to 2·10^9 steps; the slot map of
one event for z = 0..16; 96 carries among the 162 event pairs to 5·10^10 steps; the gap law D' = 2D + 2 at all 23 pairs of
consecutive marker moves to 5·10^10 steps.

**Computed** (Python, `py/test_accel.py`): the accelerated simulator gives the 126 events (C at the left end on a 0)
of the direct run to 2·10^10 steps exactly, with the same step counts, z and W.

**Computed** (`py/accel.py run 1e45`): the right end of the tape is reached 83 times in 1.6·10^45 steps, never in F.
(The tick model of the simulator is no longer needed for the step bound: the Lean checker checks every tick shape the
certificate uses.)

**Heuristic**: the two counters on one clock (from the ruler sequences of the head's turning points); random words of
the same shape halt quickly.

**Open**: the tick in shift rules for all layouts, the restructure rule, why the run's words are safe, and the question.

The closed-tape-language search (`bbtools.ctl`, K up to 6) does not confine the halt to an edge: it allows `D>0 1` with
blank beyond, one cell from the right end.

## The certificate

Lean cannot run 10^70 steps one at a time, so `py/accel.py cert` writes a certificate and `lean/Cert.lean` checks it.
The configuration is kept as two lists of cells. An operation is `D n` (n plain steps), `L`/`R` (a new layout of the
left or right counter: gap lengths between the digits) or `B d` (d ticks of both counters at once). Most of the run is
in the 20,226 batches; the plain steps between them are the overflows, new digits and rebuilds.

To accept `B d` the checker trusts nothing from the simulator:

1. The head must be on the base cell, a 0, in state A. The left list is cut by the layout into a first gap and digit
   pairs (`00`/`11`) with their gaps, the right list into a first gap and single digits with their gaps; the cut is
   confirmed by rebuilding both lists from it. This gives the counter values a and b.
2. A tick is three visits: right of the base cell, left, right again (arrivals at the base cell in `(A,1)`, `(E,1)`,
   `(A,0)`). The checker runs the left part for every carry length k on a window holding only the first k + 1 digits
   of L and their gaps, and the right part for every carry length j on a window with the first j + 1 digits of R. A
   window run fails if the head would leave the window, so its result holds whatever the rest of the tape is
   (`wrun_sound`). Each part must arrive at the base cell in the same states as a reference tick and end with its low
   digits incremented; G(k) and F(j) are the step counts it took. Results are cached while a layout keeps its first
   blocks, so each carry length is checked once per layout.
3. `TM.side_sound` puts the two parts together into a whole tick, `TM.tick` turns the checks into "from any a, b
   (with no carry out of the known digits) one tick adds one to both in G(tz1 a) + F(tz1 b) steps", and `TM.batch`
   into d ticks in `csum G a d + csum F b d` steps, where `cnt a d k = (a+d+2^k)/2^(k+1) − (a+2^k)/2^(k+1)` counts
   the values with k trailing ones.

## Open questions

* Prove that the right end is never reached in F: the last block is always entered in E (after a separator) and
  has length 0 or 2 mod 3 in the words the rebuilds write, which end in `(110)^13 111`.
* Decode one tick (a sweep of L's last digit and R's last bit, then the carries) as shift rules and prove them in
  Lean; that would make the overflow law a theorem `(z, R) -> (z + 1, R + 2^z)` for all z.
* The restructure: it is set off by R's overflow at a time fixed by R, and copies L. A rule for it, as a function of
  (z, L, W), would give an epoch-to-epoch map and an accelerated run over many epochs.
* Which words reach the halting configuration `D>0 1` at the right end, and whether a restructure can write one.

## Layout

| path | what it is |
|---|---|
| `lean/Machine.lean`, `lean/Blank.lean` | the machine, the halting configurations and bounded runs (generated) |
| `py/overflows.py` | the overflow events as (z, W), the carry law check, the slot experiment, the end-of-epoch prediction |
| `lean/Edge.lean`, `lean/EdgeHalt.lean` | the right sweep through the last block and the halt at the end of the tape |
| `py/gen_edge.py` | generates `lean/Edge.lean` with `bbtools.symtm` |
| `py/accel.py` | the accelerated simulator (two learned binary counters, ticks applied arithmetically), its right-end log, the certificate writer |
| `py/test_accel.py` | its test against `tools/c/tmrun.c` (events to 6·10^9 steps by default) |
| `lean/Tick.lean` | window runs, two-sided ticks and batches of counter ticks, with their soundness (any machine) |
| `lean/Cert.lean` | the certificate checker for this machine and `checkCert_sound` |
| `lean/Long.lean`, `lean/cert.txt` | the certificate and the theorem: no halt in 1.2·10^70 steps (`native_decide`) |
| `py/tmsim.py` | a plain simulator started from a given tape, run to the next event |

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB 100000000000 records 100000
./tmrun 1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB 2000000000 at C L 1000 > ev.txt
python3 holdouts/1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/py/overflows.py check ev.txt
python3 holdouts/1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/py/overflows.py slots ev.txt 17857444 0 17
python3 holdouts/1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/py/test_accel.py 2e10
python3 holdouts/1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/py/accel.py run 1e45
python3 holdouts/1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/py/accel.py cert 1e70 cert.txt   # 9 minutes; = lean/cert.txt
```

## Pages

- [`pages/holdouts/1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/explainer.html`](../../pages/holdouts/1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/explainer.html)
- [`pages/holdouts/1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/proof-status.html`](../../pages/holdouts/1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB/proof-status.html)
