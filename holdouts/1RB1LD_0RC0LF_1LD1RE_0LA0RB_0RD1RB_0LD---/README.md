# 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---

bbchallenge id 173741. One of the six-state holdouts whose halting from blank tape is open. Family: Carry system: binary counters in 4-cell digits (left) and 3-cell digits (right), halting on the pattern >0111.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LD |
| B | 0RC | 0LF |
| C | 1LD | 1RE |
| D | 0LA | 0RB |
| E | 0RD | 1RB |
| F | 0LD | --- |

**Verdict.** **The question is open.** No halt in the first 10^10 steps (C simulator). The whole machine is a carry system of eight local rules on the tape, each proved in Lean (round 6, below). It halts exactly when state B comes to stand in front of `0 1 1 1`, and the only rule that can bring it there (R1) was used 424 times in the first 10^10 steps, each time in front of a 0. The right half as a whole has not been turned into numbers, so the question has not become arithmetic.

## What it does

The head shuttles around the start cell. Each round trip goes once left and once right.

- **Left half: a binary counter of round trips.** From the left end: an optional `10`, then 4-cell digits `1010` (one)
  and `1000` (zero), least significant next to the centre, then a `1`. Each visit adds one
  (`L 1000 (1010)^n 1 D>0 R -> L 1010 1 (0001)^n E>0 R`, proved for all n). An all-ones counter overflows in two
  half-steps (with and without the prefix `10`), so the left end grows exactly when the number of round trips T is
  2^k or 3·2^(k-1). Checked for all 8,388,630 visits in 10^9 steps.
- **Right half: a chain of counter segments.** Binary counters with 3-cell digits (`100`/`010`/`001` for one, `000` for
  zero, the phase depending on the segment), separated by markers like `101`; the lowest one changes every round trip and
  carries into the next. At each growth of the left counter the lowest segments are re-laid (one gains a digit and
  changes phase). The right end grows at irregular T (974, 1277, 1405, 1903, ..., 14,168,192).
- **Halting** needs F reading a 1 (`0 1 F>1 1`), and F does not occur in the left counter's moves, so a halt would have to happen right of the left counter.

<!-- F02-visit-law:begin -->
## The visit law, and where the run leaves the PR59 machines (F02, 13 November 2026)

**Proved in Lean (kernel), `lean/Visit.lean`.** A *visit*: the head enters a stream `s` (all cells from some cell on)
in state C with a 0 on its left, and comes back in state A two cells further left, the 0 restored and `s` rewritten
to `v(s)`. `Vis s s'` says exactly that, for every tape to the left. The rules, for every stream `s`:

| stream | after the visit | theorem |
|---|---|---|
| `0 s` | `1 s` | `vis_0` |
| `100 s` | `000 v(s)` | `vis_100` |
| `110 s` | `000 v(s)` | `vis_110` |
| `1010 s` | `1010 v(v(s))` | `vis_1010` |
| `1011 s` | `1000 s` | `vis_1011` |
| `111 s` | the machine halts | `vis_111_halts` |

`111 s` halts the machine (`vis_111_halts`). The six prefixes 0, 100, 110, 111, 1010, 1011 cover every stream, so the
rules are the whole machine: it halts from blank tape only if some visit meets `111` (each rule is a theorem; this
"only if" is read off the case list and is not itself stated in Lean).

The run is a sequence of rounds (`start`, `round`, `round_halts`): after 4 steps the tape is `0^inf A> 1 0 S_1` with
`S_1 = 1 0^inf`, and a round turns `0^inf A> 1 0 S` into `0^inf A> 1 0 S'` with `S' = v(1 0 S)`. If a nested visit
halts, so does the visit around it (`vis_100_halts_1`, `vis_110_halts_1`, `vis_1010_halts_1`, `vis_1010_halts_2`).

**The same first four rules as the machines of busycoq PR59.** `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---` and its two
relatives obey `0 s -> 1 s`, `100 s -> 000 v(s)`, `110 s -> 000 v(s)`, `1010 s -> 1010 v(v(s))` too, with the same
rounds; they halt on `1011` (on `111` the three differ). PR59 proves in Rocq that they halt: rounds 1 to 161,210 use
only those four rules and round 161,211 meets `1011`. This machine differs only in what it does on `1011` and `111`.

**Computed (not proved): this machine does not halt there.** `c/vis.c` in
`../1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---/` runs the visit law with counts (2^j visits cross the word
in round 2j; counts are kept as 2^e - c). It learns every rule from the machine's own table, by direct simulation of a
visit, and falls back to direct simulation for anything without a rule. Checks: against a direct run of the machine
(every top-level visit of the first 3·10^7 steps, `py/vis_check.py`), against the same algorithm with exact integers
(`py/vis.py`, 1,500 rounds, same tape), and on the PR59 reference machine it halts in round 161,211 on `1011`, as PR59
proves. Result: rounds 1 to 161,210 use the four shared rules only; round 161,211 meets `1011` at the right end of
the word, rewrites it to `1000` and the run goes on. Observed: no halt and no visit to `111` up to round 200,000
(the run is still going; each further 100,000 rounds costs more than the last, the cost grows with the square).

A guess at how `1011` arises (not checked against the run): a count that dies exactly on a block leaves a stale
`110`; a later round whose blocks are aligned two cells earlier reads `0011`, writes `1011`, and comes again. Aligned
one cell earlier it would read `011` and then `111`. Nothing we know excludes a halt of this kind, and nothing proves one.

Tools (all in `../1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---/`): `py/visit.py MACHINE NAMESPACE OUT` writes
`lean/Visit.lean` by symbolic execution; `c/vis.c` (`gcc -O2 -o vis c/vis.c; ulimit -s unlimited; ./vis MACHINE [TOPVISITS [DUMP]]`,
two top-level visits per round for machines whose A1 is 0LB, one for A1 = 1LD); `py/vis.py`, `py/vis_check.py`.
<!-- F02-visit-law:end -->

## What is established

**Proved in Lean, kernel only:**

- **The halting configurations.** The machine stops exactly when it reads the symbol of a halting transition (F1); the generated statement covers every configuration. (`step_none_iff`, `lean/Blank.lean`)
- **No halt in the first 10,000 steps.** The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel. (`blank_runs_kernel`, `lean/Blank.lean`)
- **The three moves of the left counter.** For every n and any tape around them: **increment** `L 1000 (1010)^n 1 D>0 R` reaches `L 1010 1 (0001)^n E>0 R` (n trailing one-digits become zero-digits, the zero-digit before them becomes a one); **overflow without prefix** `0^inf (1010)^n 1 D>0 R` reaches `0^inf 1 0 1 (0001)^n 0 D> R`; **overflow with the prefix 10** `0^inf 1 0 (1010)^n 1 D>0 R` reaches `0^inf 1 0 1 0 0 (0100)^n 0 C> R`. Each is a theorem about the machine's step function with an exact step count. (`left_increment`, `left_overflow_even`, `left_overflow_odd`, `lean/Rules.lean` (generated by `py/gen_rules.py`))

**Proved in Lean with `native_decide`:**

- **No halt in the first 10^7 steps.** The same run, evaluated by compiled code. (`blank_runs_native`, `lean/Blank.lean`)

**Trusted computation (C/Python, not Lean):**

- **No halt in the first 10^10 steps.** The C simulator `tools/c/tmrun.c` runs 10^10 steps from blank tape without a halt; at the end the tape holds only 91 ones. (`tmrun 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD--- 10000000000`)
- **No halt in the first 10^9 steps.** The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 252 cells have been visited and 77 of them hold a 1. (`holdouts/triage.json`)
- **Where a halt can be.** A closed tape language of windows of 5 cells (`tools/py/bbtools/ctl.py`, closure checked by the script, not by Lean) contains every configuration reachable from blank tape, and its only halting configurations have F reading a 1 with a 0 and then a 1 left of the head and a 1 right of it (`0 1 F>1 1`). (`python3 -m bbtools.ctl 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD--- 5`)
- **The left half is a binary counter of round trips.** Every time D reads the 0 at cell 1 with a 1 at cell 0 (the head about to visit the left half), the cells from the left end to cell 0 read `(10)? w 1` with `w` a word of 4-cell digits `1010` (one) and `1000` (zero), least significant digit next to the centre. In the first 10^9 steps this happens 8,388,630 times and every time the number `w` is one more than the time before, except 45 growth moves, all of the two kinds above: `10`+all ones (b digits) becomes all ones with b+1 digits and no prefix, which overflows at the next visit to `10` + b+1 zeros. (`c/leftchk.c` | `py/leftdec.py` (see Reproduce))
- **The left end grows at 2^k and 3·2^k−1 round trips.** Counting the visits above as round trips T = 1, 2, 3, ..., the left end of the tape grows (by two cells) exactly when T is 2, 3, 4, 6, 8, 12, 16, 24, ..., 2^k, 3·2^k−1, ... up to T = 12,582,912 (all 46 growths in the first 10^9 steps). A round trip costs 135 to 225 steps on average, so the left end grows like the logarithm of the step count. (`c/rightgrow.c`)
- **Not decided by n-gram CPS up to width 14.** The n-gram Closed Position Set decider (`tools/c/ngramcps.c`) with equal widths 4, 6, 8, 10, 12 and 14, plain and with the fixed-length (1) and LRU history augmentations, either reaches a halting local configuration (UNKNOWN) or stops at 3·10^7 local configurations: it does not prove non-halting at these settings. (`ngramcps MACHINE N [-H 1 | -U] -m 30000000`)

**Heuristic:**

- **Growth shape: exp/exp.** Left of the start, the visited part of the tape grows like the logarithm of the step count: each new cell costs a roughly constant factor more time, the signature of a *counter* or of a Collatz-like map whose values are written on the tape (fitted exponent 0.075). Right of the start it grows like the logarithm of the step count: each new cell costs a roughly constant factor more time, the signature of a *counter* or of a Collatz-like map whose values are written on the tape (fitted exponent 0.065). (`tools/py/bbtools/triage.py`)
- **A gap growing by 3.** At the left records at 9.9·10^7, 1.4·10^8, 2.0·10^8 and 2.7·10^8 steps the longest gap shortly after the (1 0)^n stretch has 19, 22, 25 and 28 zeros. This gap is the lowest right-hand segment emptied out (all digits `000`) just after an overflow, and it gains one 3-cell digit per growth. (`tmrun 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD--- 1000000000 records 100000`)
- **The right half: a chain of counter segments.** Right of the centre the tape is a chain of segments, each a binary counter with 3-cell digits (one of `100`, `010`, `001` for a one, depending on the segment, and `000` for a zero), least significant digit nearest the centre, separated by short markers such as `101` and `010 100`. The lowest segment changes on every round trip; a segment that overflows carries into the next one. At each growth of the left end the lowest segments are re-laid (one segment gains a digit and changes its phase). The right end grows at irregular values of T (974, 1277, 1405, 1903, ..., 8,360,447, 14,168,192), not at powers of 2. The rule for the re-laying has not been found. (`c/rightgrow.c`; read off snapshots, not checked mechanically)

**Open:**

- **Does it halt from blank tape?.** Not known. The macro configuration family has not been found.

## The carry system (round 6)

The community tracker says this machine is "equal to Beaver Math Olympiad problem 10, a seven-rule carry system",
with rules proved in Rocq. We have not seen that statement. What follows is our own derivation from the table; it
has eight rules and the halting pattern, and we cannot say how the Olympiad's seven rules group them.

Write `>` for the head in state B about to read the next cell (moving right) and `<` for the head in state D on the
cell before the mark (moving left). From one such moment to the next the machine does exactly one of:

| rule | before | after | steps | in words |
|---|---|---|---|---|
| R1 | `>011` | `011>` | 3 | pass over 011 |
| R2 | `>0100` | `011>0` | 5 | a digit one becomes 011 and the hit moves on: a carry |
| R3 | `>0101` | `0100>` | 4 | erase the 1 after 010 and go on |
| R4 | `>00` | `0<1` | 2 | turn round on 00, leaving 01 |
| R5 | `0>1` | `<00` | 2 | erase a 1 and go back two cells |
| L1 | `10<` | `<10` | 2 | skip a pair 10 |
| L2 | `00<` | `1>0` | 2 | turn round on 00, leaving 10 |
| L3 | `1<` | `0>` | 1 | erase a 1 and turn round |
| halt | `>0111` | | 5 | R1 in front of a 1 |

The start from blank tape is `1>` (one step of state A). The cases are complete: B reads 1 (R5, or the halt when
the cell on its left is 1), or 00, 011, 0100, 0101; D reads 1, or a 0 with a 1 or a 0 on its left.

**Proved in Lean, kernel only** (`lean/Carry.lean`, generated by `py/gen_carry.py`; plain words for what each theorem says):

- `r1`, `r2`, `r3`, `r4`, `r5_0`, `r5_1`, `l1_0`, `l1_1`, `l2`, `l3`: each rule of the table above, as a statement
  about the machine's step function: from the configuration on the left the machine reaches the configuration on the
  right in exactly the stated number of steps, for every tape around the cells shown. (R5 and L1 are stated twice,
  once for each value of the cell the head lands on.)
- `halt_pattern`: from B about to read `0 1 1 1` the machine halts four steps later, whatever else is on the tape.
  That every halt comes about this way is an argument on paper, read backwards from the table: F is entered only from
  B on a 1, and a B that reads a 1 with a 1 on its left was entered from E on a 1, E from C on a 1, C from B on a 0.
- `carry`: for every k, after a 1, the block `(010)^(k+1) 00` hit by B becomes `(000)^(k+1) 01` with D back on its
  first cell, in 10k + 12 steps. With `010` as the digit one and `000` as zero, lowest digit first, this is binary
  addition of one with a carry through k+1 ones.

**Computed (trusted Python/C, not Lean):**

- The rules replay the run. `py/carry_system.py` knows only the eight rules; 3·10^7 applications stand for 73,332,821
  machine steps, and at every millionth application the tape, head and state equal the plain machine's. Rules used:
  L1 10,000,057; L2 3,333,457; L3 3,333,200; R1 218; R2 3,332,982; R3 3,333,428; R4 3,333,458; R5 3,333,200.
- R1 is rare. R1 is the table entry E1. In the first 10^10 steps it is used 424 times (5 in 10^3 steps, 18 in 10^4,
  46 in 10^5, 90 in 10^6, 148 in 10^7, 228 in 10^8, 306 in 10^9), first at step 77, and each time the cell after the
  `011` is 0. A halt can only happen at one of these moments.

**How the rules count.** A hit on `000` (after a 1) turns round at once and leaves `010` (R4, L1). A hit on `010`
makes it `011` and passes the hit on (R2); when the hit finally turns round, the way back erases every `011` to `000`
(L1, L3, R5 in turn). The left half does the same with pairs: L1 skips pairs `10`, L2 turns the first `00` into
`10`, and R3 on the way back turns every second pair into `00`: the binary counter of round trips in 4-cell digits
(`1010` one, `1000` zero) that `lean/Rules.lean` already proves. In a plain block of digits R1 never fires, because
`011` exists only while a carry is on its way. In the round trips we traced by hand it fires where blocks of different alignment meet on the
right; which meetings can occur is the part that is not understood.

**The open question, as far as we can state it.** Does the rewriting system above, started from `1>` on blank
tape, ever reach `>0111`? We do not have it as a statement about numbers: that needs the right half described as a
list of counters with the rule for what happens where they meet, and we have not found it.

**The proved neighbours.** In the copy of busycoq we read, three machines one entry away from this one are proved:
E1 = `0RF` (`verify/SOMDCv1.v`, module TM13: a closed family of configurations with period 7, non-halting), E1 = `1RF`
(`verify/RRBAv3.v`, `tm455`, non-halting), and F0 = `1RD` (`verify/Eqv_v2.v`, TM511: halts exactly when the solved
machine `1RB---_0LC0RD_1RD1LB_0RE0LA_1LB1RF_0RB1RD` does). Here E1 = `1RB` is rule R1, used from step 77 on, and
F0 = `0LD` is half of rule R5, used in one rule application out of nine. Both entries are reached from blank tape, so
none of these proofs carries over by "the differing entry is never used".

## For later

With the carry system in hand: parse the right half at the moments R1 fires (`py/carry_system.py` can print them) into
blocks of 3-cell digits and the cells between them, and look for the rule that says what stands after an `011`. A first observation: of the 144 uses of R1 in the first
3·10^6 rule applications, 78 come as R3, R4, L2, R1 on `>0101001`, which becomes `0101011>`; so `>01010011` would
halt, and the question there is whether `11` can ever stand after `010100`.

Earlier note: The re-laying rule of the right segments at the growth moments of the left counter. Record the right half at the
46 growth moments (`c/rightgrow.c` prints it before and after), parse it into segments (marker, phase, width, value),
and look for the map between consecutive growth moments; then prove the carry through each kind of marker with
`bbtools.symtm.prove`. A full macro rule would turn this into an induction on T.

## Reproduce

From the repository root:

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/lean/check.sh
gcc -O2 -o triage tools/c/triage.c && ./triage 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD--- 1000000000
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD--- 10000000000
cd tools/py && python3 -m bbtools.ctl 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD--- 5
python3 holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/py/gen_rules.py | diff - holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/lean/Rules.lean
gcc -O2 -o leftchk holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/c/leftchk.c && ./leftchk 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD--- 1000000000 | python3 holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/py/leftdec.py
gcc -O2 -o rightgrow holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/c/rightgrow.c && ./rightgrow 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD--- 1000000000 | grep ^A
python3 holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/py/gen_carry.py | diff - holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/lean/Carry.lean
python3 holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/py/carry_system.py 30000000 1000000
g++ -O2 -o transcount holdouts/1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB---/c/transcount.cpp && ./transcount 1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD--- 10000000000 E1
```

## Pages

- [`pages/holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/explainer.html`](../../pages/holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/explainer.html)
- [`pages/holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/proof-status.html`](../../pages/holdouts/1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---/proof-status.html)

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same tapes at another pace (observed, not proved).** Leave the states aside and compare only the tape and the place of the head. Then a large part of the first 10^7 configurations of this machine are configurations of the machines below, in the same order and up to the end of the run. The steps at which they occur differ, the tables are not renamings of each other, and equal tapes with different states may be continued differently, so this does not tie the halting questions together.

- [`1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---`](../1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---/README.md): 7,916,051 configurations, the last at step 9,165,688 here and step 10,000,000 there
- [`1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---`](../1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---/README.md): 7,916,520 configurations, the last at step 9,166,232 here and step 10,000,000 there
- [`1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---`](../1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---/README.md): 7,916,520 configurations, the last at step 9,166,232 here and step 10,000,000 there
- [`1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---`](../1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---/README.md): 6,666,345 configurations, the last at step 9,165,397 here and step 9,999,999 there
- [`1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---`](../1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---/README.md): 7,916,289 configurations, the last at step 9,165,962 here and step 10,000,000 there

<!-- end of related machines -->
