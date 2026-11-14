# 1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD

bbchallenge id 25899. One of the six-state holdouts whose halting from blank tape is open (group G07).
Family: **marker crawling through blocks of 2s, with signal events that rebuild the tape**. Decision: **open**.

In one sentence: a marker crawls through a growing block of 2s and eats the markers in front of it; each time it turns
into a signal 1, one long excursion rebuilds the block and part of the tail, and that excursion ends in a rebuilt
tape, in a full reset `4 2^N`, or in a halt, the last two only when the block and the tail fit exactly
(`2^(4b+3) 1 2^b 1` resets, `2^173 1 2^42 1` halts; the machine itself passed `2^171 1 2^42 1` at step 219,107).
An exact accelerated run finds no halt in 10^300 steps.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RF |
| B | 1LC | 1LF |
| C | --- | 1LD |
| D | 1LE | 0RA |
| E | 1RE | 1LB |
| F | 1RD | 0LD |


## What it does

Read the tape as runs of 1s separated by single 0s and write each run as its length: the tape becomes a list of
digits, almost all 2 (`110`), with a few markers 1, 3, 4, 6, 7, 10. The head sweeps across the whole list and back;
each round trip adds one digit at the left end (the left end grows like the square root of the step count, the
right end has not moved since about 10^7 steps).

**The marker.** A 3 inside a block of 2s moves one digit right every two sweeps, through the intermediate form 6
(the cells `111 0 11` become `111111` and then `11 0 111`):

    3 2  ->  6  ->  2 3

With the head at the left end in state D (`Mk a b R = 0^inf D> 0 0 (110)^a 1110 (110)^b R`):

    Mk a (b+1) R  ->  Mk (a+3) b R    in 24a+70 steps          (lean/Rules.lean `marker`, lean/Phase.lean `marker'`)

and `markers` in Phase.lean iterates it: Mk a (b+j) R reaches Mk (a+3j) b R. The block in front of the marker
loses one digit, the block behind it gains three (one from the marker, two grown at the left end).

**Collisions and signals.** Every local change between two consecutive visits of the left end, collected over the
first 3·10^8 steps (`py/rules.py` proves the marker; the table comes from comparing consecutive tapes):

| before | after | | before | after |
|---|---|---|---|---|
| `3 2` | `6` | | `3 3` | `7` |
| `6` | `2 3` | | `7` | `2 4` |
| `6 3` | `2 3 3` | | `4` | `2 1` |
| `3 6` | `10` | | `10` | `2 7` |
| `3 1` | `5` | | `5` | `2 2` |

(each rule keeps the number of cells: `3 3` = `111 0 111` = 7 cells = `7`). So when a marker reaches the next one,
they merge and decay into a 1: `6 3 -> 2 3 3 -> 2 2 7 -> 2 2 2 4 -> 2 2 2 2 1`. A 1 is a fast signal: in one
sweep it crosses a whole block of 2s and turns into a 6 (a new marker) at the far end. Rarely, the head stays in
one of the other phases for a whole sweep and a long block at the left end is rebuilt at once; these *epochs* start
from `0^inf D> 0 1111 0 (110)^N ...` with N = 2, 8, 214, 1220, 2528, 7645 (steps 59, 4111, 331,768, 13,012,071,
92,514,139, 480,853,980), and the list of blocks and markers on the right is reorganized at each.

## Fourth pass: signal events, and an exact run to 10^300 steps

**The tape at left-end visits.** At each new leftmost cell reached in state D (`c/dv.c`) the tape, in run lengths, is

    2^n  M  TAIL          TAIL = 2^b1 m1 2^b2 m2 ... 1

and only the first marker M moves (3 -> 6 -> 2 3, one digit right per two visits, n grows by 3 per two visits); the
markers of the tail stand still. When M reaches the next marker they merge and decay (`3 3 -> 7 -> 2 4 -> 2 2 1`)
into a **signal** 1 at the end of the block. Then the head does not come back to the left end for a long time: one
*signal event* rebuilds the block and the left part of the tail. All signal events to 4*10^10 steps:

| step | before | after (next visit) |
|---|---|---|
| 7,931 | `2^30 1 2^11 3 2 1` | `2^39 6 2^2 3 2 1` |
| 17,074 | `2^52 1 2 1` | `2^4 6 2^28 3 2^14 6 2^8 3 2 1` |
| 68,143 | `2^95 1 2^14 6 2^8 3 2 1` | `2^39 6 2^41 6 2^42 1` |
| 219,107 | `2^171 1 2^42 1` | `4 2^214` (**full reset**, step 331,768) |
| 8,958,378 | `2^1221 1 2^59 3 2 3 2^24 3 2^14 6 2^8 3 2 1` | `4 2^1220 6 2^32 6 2^52 1 2^14 6 2^8 3 2 1` |
| 66,841,200 | `2^3668 1 2^32 6 2^52 1 2^14 6 2^8 3 2 1` | `4 2^2528 3 2^366 6 2^152 3 2^436 3 2^30 6 2^116 3 2^18 6 2^66 3 2^34 6 2^42 1` |
| 323,002,199 | `2^7590 1 2^366 6 2^152 3 2^436 3 ...` | `4 2^7645 6^2 2^653 3 2^244 3 2^30 6 ...` |
| 2,586,455,459 | `2^22943 1 6 2^653 3 2^244 3 2^30 ...` | `4 2^11138 3 2^8019 6 2^3429 3 2^843 6 2^349 3 2^201 6 2^49 6 2^40 3 2^34 6 2^42 1` |

Inside an event (`c/turns.c` prints the tape at the head's turning points) a wall `3` retreats through the block two
digits per round trip while the part behind it is rewritten, several passes in a row; the block is cut into pieces
whose sizes depend on n and on the tail. The event is not an affine function of the counts.

**A signal event can halt.** Started from tapes of the same form (`c/syn.c`, the plain machine from a run list):

- `2^173 1 2^42 1` **halts** after 299,509 steps (head at the blank left end in state B). The machine itself was at
  `2^171 1 2^42 1` at step 219,107, and that tape resets to `4 2^214`.
- Single-block tails `2^n 1 2^b 1`, n = 40..59, b = 0..24 (500 tapes): almost all are rebuilt; **`n = 4b+3` gives the full
  reset `4 2^(5b+4)`** (also checked for 13 values of n up to 399); a halt for (n, b) = (40, 8), (45, 10), (48, 11),
  (49, 1), (53, 12), (56, 3), (56, 13), and for n = 8j+5, b = 2j at n = 173, 181, 221, 261, 301 but not at 61, 101,
  141, 341, 381.
- The reset tapes themselves: `4 2^N` halts for N = 5 (after 524,398 steps) and N = 8 (8,684 steps); N = 2 is the
  machine's own tape at step 59 and leads to `4 2^214`.
- With the tails of the other real events and n changed by -8..8, no halt.

So a halt, like a full reset, needs the block and the tail to fit exactly: the excursion must use up the block and the
tail at the same moment. The run from blank tape hit the reset line once (n = 171 = 4*42+3).

**Exact accelerated run.** `c/msim.c` / `py/msim.py`: the tape in blocks of 3 cells on a fixed grid, run-length coded;
the head crosses a run of equal blocks at once when it leaves a block on the far side in the same state with the
same block behind it; on top of that, linear cycle jumps at the head's turning points, with the condition under which
they are exact stated in the file (every count that moves stays above the number of macro steps of a cycle). The C
version agrees with the plain machine (state, head, tape hash) at 12,569, 1,000,612, 300,013,355 and 2,000,125,467
steps, with and without jumps at 10^13 and 3*10^15 steps, and with the Python version (unbounded integers) at 10^18
and 10^36 steps: step count, macro steps and tape (`py/msim.py check`). Result: **no halt in 10^300 steps**
(`py/msim.py run 300`, 26 minutes, 108 million macro steps and 521,000 jumps); the tape then has about 800 runs of blocks.

**Heuristic.** n grows by a factor of about 3 per event and the events are about a decade of steps apart. A halt
needs an exact fit between numbers of that size, so if the fits behave like chance its probability per event falls
like 1/n and the sum over all events converges: the machine probably never halts, but nothing here proves it.
The fit is between n and the first block of the tail only: of the 3,072 tapes `2^n 1 2^b1 m 2^b2 1` with n = 40..71,
b1 = 1..12, m = 3 or 6 and b2 = 4, 9, 20, 41, 41 halt, 36 of them with b1 within 1 of n/4 - 2 (for example
n = 48, b1 = 10, m = 6 with every even b2), whatever the length of the second block. In the real events the first
block of the tail was 11, 1, 14, 42, 59, 32, 366, 0 for n = 30, 52, 95, 171, 1221, 3668, 7590, 22943: it hit the line
once, at n = 171, on its reset side. (The tail itself keeps growing: the smallest number of runs of blocks on the tape
within each decade of steps is 3 or 4 up to 10^7 steps, 17 at 10^9, 33 at 10^15, about 100 at 10^36 and about 220
at 10^90.)

## Where it could halt

The machine halts only on C reading 0, and C is entered only from B reading 0 (B writes 1 and moves left). So a
halt needs B to read a 0 with another 0 on its left. Inside the digit list every 0 is single, so this can only
happen at the left end of the tape: the head arriving at the blank left end in state B (the CTL search of
`bbtools.ctl` with K = 6 confirms that its halting configurations have blank tape on the left). In the run the
head always arrives at the left end in state D, E or F, so a halt needs an unusual epoch event.

Tape samples (runs of 1s separated by single 0s, left to right; `a^k` is k runs of length a; a long middle is cut with `...`):

- step 10,000,000: `1 2^584 3 2^365 4 2^123 6 2^178 6 2^52 1 2^14 6 2^8 3 2 1`
- step 100,000,000: `1 2^1095 4 2^270 6 2^2072 3 2^366 6 2^152 3 2^436 3 2^30 6 2^116 3 2^18 6 2^66 3 2^34 6 2^42 1`
- step 1,000,000,000: `1 2^10415 4 2^975 3 2^3848 6^2 2^653 3 2^244 3 2^30 6 2^116 3 2^18 6 2^66 3 2^34 6 2^42 1`

## Status

Open. Proved in Lean: the halting configurations, no halt in 10^7 steps (`lean/Blank.lean`), the marker rule and its
iteration (`lean/Rules.lean`, generated by `py/rules.py` with `bbtools.symtm`; `lean/Phase.lean`). Found by
simulation (not proved): the collision and decay rules in the table, the epoch starts. Not understood: what decides
the epoch events and the sizes N, so there is no macro map yet.

- **Kernel:** `step_none_iff`, `blank_runs_kernel` (`lean/Blank.lean`), `marker`, `marker'`, `markers`.
- **Trusted computation:** no halt in 10^300 steps (`py/msim.py`, exact macro run with linear cycle jumps,
  validated as above); the table of signal events; the halting and reset tapes of the fourth pass.
- **Heuristic:** a halt needs an exact fit whose probability falls geometrically from event to event.
- **Open:** whether it halts. A proof of non-halting needs the signal event as a map on (n, tail) and an invariant
  that keeps the run off the halting fits.

### Next steps

- Describe a signal event exactly: the passes of the retreating wall as a rewriting system on run lists at the
  head's turning points (`c/turns.c`), then the conditions for halt and reset in closed form (the reset line
  n = 4b+3 and the halting points above are the data).
- Find the rule for the epochs: the tape just before each epoch start as a function of the previous one (the
  block sizes N = 214, 1220, 2528, 7645 suggest sums of block lengths), then the map between epochs.
- Prove the collision rules with symtm as rules between visits of the left end, and a CTL certificate restricted
  to the digit language (digits 1-7, 10 separated by single 0s).

## Pages

- [`pages/holdouts/1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD/explainer.html`](../../pages/holdouts/1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD/explainer.html)
- [`pages/holdouts/1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD/proof-status.html`](../../pages/holdouts/1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD/lean/check.sh
cd holdouts/1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD
python3 py/msim.py check                 # macro simulator against the plain machine, jumps against no jumps, C against Python (40 s)
python3 py/msim.py run 100               # no halt in 10^100 steps (2 min); run 300 takes 26 min
gcc -O2 -o /tmp/dv c/dv.c && gcc -O2 -o /tmp/syn c/syn.c && gcc -O2 -o /tmp/turns c/turns.c
/tmp/dv 1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD 1e9 D | grep -A1 ' 2^[0-9]* 1 '      # the signal events
echo "0^2 2^173 1 2^42 1" | /tmp/syn 1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD 1e9 f D   # HALT 299509
echo "0^2 2^171 1 2^42 1" | /tmp/syn 1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD 1e9 f D   # 112661 0 4 2^214
/tmp/turns 1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD 31500 16445 6                       # inside the event at step 17,074
```

## Accelerated run

Trusted computation: `python3 tools/py/bbtools/rleaccel.py 1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD 6 169000000` runs 169,000,000 macro steps from blank tape without a halt, more than 9.71·10^13
machine steps (tape: 12,705,084 cells). The simulator codes the tape in runs, crosses a run in one step and jumps cycles whose
one-cycle rule it has first proved symbolically; it is tested cell for cell against direct runs
(`tools/tests/test_rleaccel.py`).
