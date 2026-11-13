# 1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC

bbchallenge id 74982, one of the six-state holdouts (group G06: one side of the tape stops growing, the other grows
like a square root). Whether it halts from blank tape is open. What it does is now known exactly up to an event
about 2·10^20 steps in, and the question after that has a sharp form.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RD |
| B | 1LC | 0RA |
| C | 1LF | 1LD |
| D | 0RE | 0LC |
| E | --- | 1LB |
| F | 1RB | 1RC |

## What it does

After the first 40,000 steps the tape is two pieces:

```
0^inf  (10)^n   x0 1 x1 1 x2 1 ... x110        n grows by one per sweep, x0 = 1
       wall     counter (221 cells, fixed in place)
```

- **The wall** is n copies of `10`. The head crosses it twice per sweep: state A runs right (two steps per pair),
  D, C, F run left (four steps per pair), and at the blank end the wall gains one pair. A sweep costs 6n + 4 steps
  plus the work in the counter, so after N sweeps about 3N^2 steps have run: that is the square-root growth on the
  left.
- **The counter** holds a digit x_i on every even cell and a 1 on every odd cell. Each time A arrives at x0, the
  head works its way into the counter and back, and the digits change by a fixed rule: the 4-state automaton

  | state | digit 0 | digit 1 |
  |---|---|---|
  | a (start, at x1) | write 1, stop | write 0, go to b |
  | b | write 1, go to a | write 0, go to c |
  | c | write 0, stay in c | write 1, go to a |

  read on x1, x2, ... ("stop" is the identity state e: the head turns back). It is a carry: in a, a 0 becomes 1 and
  the carry ends; a 1 becomes 0 and the carry moves on in b; and so on. On the machine this is a zigzag to the right
  (in a stretch of ones, 7 steps per three cells: `zig`) and a pass back.

So the machine is a counter ticked once per round trip of a bouncer. The automaton is a *causal permutation*: digit
i of the result depends only on digits 1..i, and on the digit strings of each length it is a bijection whose cycles
have power-of-two lengths (an odometer-like map, but not a single cycle). The carry goes deep only rarely: x1 changes
every sweep, and the first sweeps that reach x10, x40, x70, x100 are sweeps 3, 1,635, 402,291 and 69,230,963 after
step 2·10^7 (`c/counter.c`).

## When the carry reaches the end: the event system

The counter is `x0 1 x1 1 ... xk 1 d`: the digits x1..xk, each followed by a separator 1, then a last cell d with
blank tape after it. A sweep whose carry runs through all of x1..xk reads d in some state q. What happens then is
proved in Lean for every wall and every digit string (`lean/Ends.lean`):

| carry state at d | d = 0 | d = 1 |
|---|---|---|
| a | d becomes 1 (`last_stop_event`) | **extension**: one more digit 1, last cell 1 (`ext_event`) |
| b | **the machine halts** (`halt_event_b`) | **conversion** (`conv_event_b`) |
| c | **conversion** (`conv_event_c`) | **the machine halts** (`halt_event_c`) |

A conversion is what the run from blank tape does at its first end event. The pass back runs one cell out of step,
turns every separator it crosses into a digit and crosses the whole wall, turning each `10` into `11`. Afterwards a
wall of n + 1 pairs and digits xs have become

```
wall of 1 pair,   digits  1^n  0  marks(xs)  1,   last cell 1
```

where `marks(xs)` has a 1 for every digit after which the carry was in state c. Every outcome leaves a counter of
the same shape (digits with separators, then one last cell), so these five cases are all there is.

So the machine is a system of events on (wall, digits, last cell), `evstep` in Lean, and

- `halts_iff_events` (Lean, kernel only): from any arrival of this shape, the machine halts **if and only if**
  iterating `evstep` reaches a halting event;
- `blank_halts_iff_events` (kernel only): from blank tape, if and only if the event system halts from a wall of 10
  pairs, the digits `X0` and last cell 1 (step 30,225).

## The run from blank tape

Iterating the automaton (`c/counter.c`, a minute; `py/slp.py`, under a second), the carry first runs through all
109 digits at the sweep with a wall of **8,072,508,833** pairs, about **1.96·10^20 steps** from blank tape. It
reads the last cell, a 1, in state b: a conversion. `second_arrival` (Lean, with `native_decide` for the
certificate of the 8·10^9 sweeps): the machine reaches the arrival with a wall of one pair and the counter

```
1^8072508832  0  marks(Y0)  1,   last cell 1          (8,072,508,943 digits)
```

and `blank_halts_iff_second`: it halts from blank tape if and only if the event system halts from there.

The first sweep after that runs straight through the 8·10^9 ones (on ones the carry only cycles a, b, c, writing
0, 0, 1). After it the counter starts with `001` repeated 2.7·10^9 times, and the carry has to work its way through
all of that before the next end event. On the stand-in runs below the number of sweeps to the next end event
doubles about every 3 digits, so the real one is out of reach of any simulation: of the order of 2^(2.5·10^9)
sweeps.

**What kind of event comes next is not known, and it decides the question.** A halting event stops the machine,
an extension adds one digit and the next end event follows after a comparable number of sweeps, a conversion starts
the same game on a counter exponentially longer. Observed (not proved), with `py/events.py`:

- From 300 random counters of 30 to 60 digits, the events up to the first halt or conversion: 170 end in a halt,
  130 in a conversion (at most 4 events).
- From the counter after the first end event, with a stand-in wall of w pairs in place of 8,072,508,833
  (w = 1..30): 7 runs end in a halt and 23 in a second conversion, after one to three events and 4·10^9 to
  10^13 sweeps.

Nothing here says which way the real run goes: the outcome changes with w with no visible pattern.

## Status

**Open**, and reduced in Lean to a system of events on digit strings:

- `blank_halts_iff_events` (kernel only) and `blank_halts_iff_second` (with the certificate): see above. The machine
  does not halt in the first ~1.96·10^20 steps (`reaches_post`, `second_arrival`).
- `not_halts_arrival`: if no sweep ever runs through all the digits the machine never halts.
- Deciding it needs the state in which the carry first runs through a counter of 8·10^9 digits, a question about
  the automaton group generated by `a = (e, b)σ`, `b = (a, c)σ`, `c = (c, a)` on an almost periodic string.

## Proved in Lean

`lean/check.sh` checks everything below (about 45 seconds).

`lean/Rules.lean` (generated by `lean/rules.py` with symtm):

- `wall_right`, `wall_left`, `left_end`, `round`: the wall's round trip, `0^inf (10)^n D> 1 R` to
  `0^inf (10)^(n+1) A> 0 R` in 6n + 4 steps, for every n.
- `toggle`, `sweep_toggle`, `zig`: the first special cases.
- `fwd_a1`, `fwd_b0`, `fwd_b1`, `fwd_c0`, `fwd_c1`: one digit of the carry on the way right. The head is in B, D or
  A for automaton state a, b or c, with the previous pair still pending (`0 1`, `0 0`, `1 0`).
- `stop0`, `stop1`: the carry stops on a 0 in state a.
- `back_*`: state C on the way back turns each pending pair into its digit. `back_end`: back across the wall to the
  next arrival, 6n + 7 steps.

`lean/Sweep.lean` (by hand): `sweep`, **one sweep is one step of the carry automaton, for every digit string**.
The arrival `0^inf (10)^(n+1) A> 1 1 x1 1 ... xk 1 R` reaches `0^inf (10)^(n+2) A> 1 1 y1 1 ... yk 1 R` whenever
the carry `carry .a xs = some ys` stops inside the digits. The proof is by induction over the digit list (`run`).

`lean/Orbit.lean` (by hand): many sweeps at once.

- `sweeps_of_trW`: the automaton becomes a transducer on words of generators (`secW`, `trW`). If `a^k` leaves no
  sections at the end of xs, then k sweeps all stop inside xs.
- `entry_sound`, `chain_sound`, `pow_sound`: a checker for straight-line programs (nodes are generators or
  concatenations of earlier nodes) with a certificate of (node, digit) entries. Every entry that passes the local
  check is right.

`lean/Cert.lean` (generated by `py/slp.py`): the certificate for a^8072508823. It has 6,010 nodes and 7,351
entries, all checked by `native_decide`.

- `sweeps_X0`: the 8,072,508,823 sweeps after the first arrival all stop inside the digits x1..x109.

`lean/Event.lean` (by hand):

- `first_arrival` (kernel): from blank tape, step 30,225 is the arrival with a wall of 10 pairs and digits `X0`.
- `arrival_sweeps`, `halts_arrival_iff`, `not_halts_arrival`: many sweeps in a row, as stated in "Status".
- `run_off`: the way right of a carry that runs off the end, for every digit string.
- `wall_left_C`: the end event's way back across the wall, `(10)^n C> 1 R` to `C> 1 (11)^n R`, for every n.
- `event` (kernel): for every n, the sweep from `0^inf (10)^(n+1) A> 1 1 cells(Y0) 1` does the following:
  - its carry runs into the last cell in state b;
  - it passes that cell without halting;
  - it reaches `post n`.
- `reaches_post`, `halts_iff_post`: put together from these.

`lean/Ends.lean` (by hand): every end event, for every wall and every digit string, and the event system.

- `exitQ`, `thru`, `cind`: the state in which a carry leaves the digits, the digits it writes, and its marks.
- `run_thru`, `thru_sweep`, `last_stop_event`, `ext_event`: the carry reads the last cell in state a.
- `halt_event_b`, `halt_event_c`: the two halting events.
- `cb_step`, `cb_all`, `ok_off`, `cunw_off`, `conv_back`, `conv_event_b`, `conv_event_c`: the conversion. `cb_step`
  is the pass back one cell out of step; `ok_off` shows that the pending pairs of a carry never stop it;
  `left_restart` starts the new wall.
- `evstep`, `evstep_some`, `evstep_none`, `halts_iff_events`, `blank_halts_iff_events` (kernel only).
- `second_arrival`, `blank_halts_iff_second`: the run from blank tape after its first end event.

`lean/Twin132695.lean` (by hand): the machine 1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC (bbchallenge 132695) is
this table in a mirror with the states renamed, so its run from blank tape is this machine's run from blank tape
started in state C.

- `mirror_step`, `mirror_steps`, `halts_mirror` (for any two tables related this way), `is_mirror`.
- `twin_arrival` (kernel): 16 steps from blank tape in state C is the arrival (wall of 1 pair, digits [1], last
  cell 1). `twin_halts_iff_events` (kernel only): 132695 halts from blank tape if and only if the event system halts
  from there.
- `twin_conversion`, `twin_halts_iff_after` (`native_decide`): after 410,976 sweeps, the last a conversion of a wall
  of 410,923 pairs. See that machine's README.

`lean/Blank.lean` (generated): the halting configurations (`step_none_iff`, E reading 0) and no halt in the first
10^7 steps.

## Computed (not proved)

- `py/slp.py` (under a second): the binary search for the first sweep that runs into x110, using a
  straight-line program for a^k (hash-consed, about 6,000 nodes for k ~ 8·10^9). It finds sweep 8,072,508,824,
  arriving in state b, the same answer as `c/counter.c`. It writes `lean/Cert.lean`.
- `py/events.py twin` (a second): the run from blank tape in state C against the event system, and its events up
  to the conversion at sweep 410,976. `py/events.py program` (under a minute): the exit states of the prefixes of a
  counter as one straight-line program, which stops compressing after about 150 digits.
- `py/events.py check` (a second): the Python copy of `evstep` against the machine itself on 20,000 random
  arrivals (walls of 1 to 7 pairs, up to 12 digits), every kind of event. `py/events.py epochs` and
  `py/events.py standin`: the statistics quoted above, with the sweeps between events jumped by straight-line
  programs.
- `py/automaton.py` (a few seconds): runs the machine from blank tape; the counter is x0 1 x1 1 ... at every arrival
  and the wall is (10)^n; a sweep run on the counter alone reproduces all 979 sweeps of the first 3·10^6 steps; finds
  the automaton (4 states) and checks it on 3,000 random 80-digit counters; checks that no counter of up to 16 digits
  makes the machine halt or break the pattern inside the counter; checks the permutation property for lengths up to
  12; and runs the end events above.
- `c/counter.c` (about a minute): the snapshot at step 2·10^7, then the automaton to the first end event; prints
  the wall length and the state.

## For later

- The state of the second end event: the first sweep that runs through `(001)^m 0 ...`, m = 2.7·10^9. The exit
  states of a prefix, as a sequence in time, are the image of the sequence a, a, a, ... under one two-state
  transducer per digit, so the question is about a product of 8·10^9 transducers of period 3. Kept as a
  straight-line program these sequences stop compressing after about 150 digits (`py/events.py program`).
- Make the certificate kernel-checkable (the string parsing does not reduce in the kernel; it would need the data as
  a balanced tree of literals).

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC/lean/check.sh
python3 holdouts/1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC/py/automaton.py
python3 holdouts/1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC/py/slp.py      # rewrites lean/Cert.lean
python3 holdouts/1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC/py/events.py check
python3 holdouts/1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC/py/events.py epochs
python3 holdouts/1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC/py/events.py standin 30   # a few minutes
python3 holdouts/1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC/py/events.py twin
python3 holdouts/1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC/py/events.py program
gcc -O2 -o counter holdouts/1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC/c/counter.c && ./counter
```

## Pages

- [`pages/holdouts/1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC/explainer.html`](../../pages/holdouts/1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC/explainer.html)
- [`pages/holdouts/1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC/proof-status.html`](../../pages/holdouts/1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC`](../1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC/README.md): rename A→D, B→C, C→A, D→E, E→F, F→B and exchange left and right; it is this table started in state C, in a mirror

<!-- end of related machines -->
