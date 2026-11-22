# 1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---

bbchallenge id 4320, group G12. Whether it halts from blank tape is **open**. Family: two-level block counter (fast tail, walker in a list of 2s, rebuilds).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0RE |
| B | 0RC | 0RF |
| C | 1LD | 1RA |
| D | 1RE | 0LD |
| E | 0LB | 1RC |
| F | 1LE | --- |


## The picture

At the moments the head is in C on a 0 just right of a 1 the tape is

    1^b0 0 1^b1 0 ... 0 1^bk 0 1^l  C>  0^g1 1 0^g2 1 ... 0^gr 1

a list of blocks (the interior), a last block l and a zone of single 1s. In a *regular* configuration b0 is a multiple
of 3, the other b_i are 2 mod 3, l is 1 mod 4, g1 is a positive multiple of 4 and the other gaps are 3 mod 4. One
*sub-round* (to the next such moment) does two independent things:

- **W** on the interior: `(..., x, 3a+2) -> (..., x+3, 2, ..., 2)` (a blocks of 2). In digits a_i = (b_i - 2)/3: drop the
  last digit a, add 1 to the one before, append a zeros.
- **the counter**: l and the zone are a binary counter; l + segments = 4m + 1 during the 2^m sub-rounds of round m
  (`enc`/`dec` in `py/model.py`).

A tail `(..., q, a)` becomes `(..., q+a+1)` after exactly 2^a steps of W, so a list with digits a_1..a_k is a single
block after exactly T = sum_i 2^(a_i + ... + a_k + k - i) steps: the list is the binary expansion of the time it has
left. All of this is proved in Lean for every size (`lean/Subround.lean`, `lean/Collapse.lean`), with the counter in a
more general form: any last block l >= 2 becomes a new gap of l - 1 cells (with the head's cell) and l = 1; with l = 1
the carry removes the leading gaps of 3, takes 4 cells from the next gap (any gap of at least 4) and sets l = 4n + 5, or,
if it meets two 1s side by side before a gap of at least 2, sets l = 4n + 4 and takes 2 from that gap.

With a single block of 3(k + 1) cells left, one sub-round (proved) cuts it into `3 2^k` and turns the last block into
a new gap of the zone (l - 4 cells). The digits of `3 2^k` give T = 2^k - 1, so on its own a rebuild brings back the
same single block after 2^k sub-rounds (`rebuild_cycle`). The single blocks grow because of the *small gaps*: the new
gap shrinks by 4 at each carry into it, and when a carry meets it at 1 or 2 cells (or 0 before 0 or 1) cells of the
counter move into the list. These few dozen sub-rounds per rebuild form the *transient*.

**One sweep machine for every sub-round.** All sub-rounds, the transients included, are the same two sweeps
(`lean/Pass.lean`, `lean/General.lean`). The left sweep erases the last block, moves the block before it one cell to
the right and adds 3 to the block before that; then the head turns right in state A. The right sweep reads the tape in
one of three phases A, E, C (the machine states) with an *open block*, the 1s just left of the head:

| phase | reads | does |
|---|---|---|
| A | 1 | writes 0: the open block closes, an empty one opens; then E |
| E, C | 1 | keeps it (the open block grows); E goes to C, C to A |
| C | 0 after a non-empty open block | the next moment: the open block is the new last block |
| C, E | 0 next to an empty open block | the two cells become `11`; then C |
| E | 0 after an open block | the open block moves one cell right, the block before it grows by 3; A again |
| A | `010` | the same, with one more 1 to read |
| A | `000` | `111`; then C |
| A | `001` | `101`: the open block closes at the middle cell (cells of the counter move into the list) |
| A | `011` | the machine halts |

W is a block of 3a + 2 read from A (`(011)^a 01`), the regular counter is A on `000` and on gaps of 3 (`0001` ->
`1111`); the small gaps are A on `001` and `010`. The function `pstep` is total and proved sound for every size and every
tape (`sub_moment`, `sub_halt`), so the only way the machine can halt is a carry that meets `011` in phase A; the halting
family below reaches the zone `4 3 ... 3 1 0` that way. With it the kernel evaluates the first two transients
(`lean/Transient.lean`), and with the counter in closed form (`lean/Counter.lean`: 4j more cells in the last block make
one counter step take 2^j) and part of a collapse read off the time left (`lean/Advance.lean`) the run from blank tape is
proved to rebuild 40, a single block of 3,483 cells after more than 2^1160 sub-rounds (`lean/Chain.lean`, 454 segments).

| rebuild | single block | sub-rounds so far | list afterwards |
|---|---|---|---|
| 1 | 36 | more than 2^10 | `3 2^6 11 5^2 2^2 5` |
| 2 | 57 | more than 2^17 | `3 2^13 11 5^2 2^2 5 2^2 5` |
| 3 | 90 | more than 2^29 | `3 2^25 14 2^2 8 2^3 5` |
| 4 | 123 | more than 2^40 | `3 2^33 17 5 2 5 2^4 11 5 2 8^2 5 2^2 8 2 5` |
| 5 | 216 | more than 2^71 | `3 2^67 14 2^2 8 2^3 5` |
| 6 | 249 | more than 2^82 | `3 2^77 11 5^2 11 5 8 2^2 5 2 5` |
| 7 | 306 | more than 2^101 | `3 2^95 14 5 2^2 5^2` |
| 8 | 327 | more than 2^108 | `3 2^102 17 2^2 5 8 2 20 2^3 8 2^4 5 2^32` |

`py/model.py run` takes regular sub-rounds by arithmetic and everything else by direct simulation (`c/trans.c`): 986
rebuilds, more than 2^105,958 sub-rounds, no halt. Tapes of the same shape do halt: `1^(3k) 0 1^(4k-3) C>0`, k = 3..9.

## What is established

**Proved in Lean, kernel only** — The halting configurations: The machine stops exactly when it reads the symbol of a halting transition (F1); the generated statement covers every configuration. (`step_none_iff`, `lean/Blank.lean`)

**Proved in Lean, kernel only** — No halt in the first 10,000 steps: The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel. (`blank_runs_kernel`, `lean/Blank.lean`)

**Proved in Lean with `native_decide`** — No halt in the first 10^7 steps: The same run, evaluated by compiled code. (`blank_runs_native`, `lean/Blank.lean`)

**Computed (trusted C/Python)** — No halt in the first 10^9 steps: The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 189 cells have been visited and 86 of them hold a 1. (`holdouts/triage.json`)

**Proved in Lean, kernel only** — Three rounds of the run, for any tape further left: Three consecutive rounds of the run from blank tape (between moments the head is in C on the first 0 right of everything written), each proved for every tape left of the cells it visits, with its exact step count. (`lean/Rounds.lean` (generated by `py/gen_rounds.py`))

**Computed (trusted C/Python)** — No halt in 3·10^10 steps; three rebuilds: Direct simulation for 3·10^10 steps. At the moments the head is in C on the first 0 right of everything written the tape is a list of blocks of 1s separated by single 0s; the last block grows by 4 per round; in walking phases the rounds satisfy T′ = 2T + 4 exactly. Rebuilds of the list at steps 72,083, 11,004,261 and 22,558,329,283 (the table). (`tools/c/tmrun.c` (`at C R`))

**Computed (trusted C/Python)** — Between rebuilds: a binary counter that applies one list operation per tick: At the moments the head is in C on a 0 just right of a 1, the tape is a list of blocks of 1s separated by single 0s (the interior), a last block l, and to the right of the head a zone of single 1s. Call it regular if the first block is a multiple of 3, the other interior blocks are 2 mod 3, l is 1 mod 4, and the gaps of the zone are 0 mod 4 (the first, counted from the head) and 3 mod 4 (the others). From one such moment to the next (a sub-round) a regular configuration changes in two independent ways. The interior takes one step W: (..., x, 3a + 2) becomes (..., x + 3, 2, ..., 2) with a blocks of 2. The last block and the zone are a binary counter: with segments s1 = g1, si = gi + 1, a last block l ≥ 5 becomes a new first segment l − 1 and l = 1; with l = 1 the n leading segments equal to 4 are removed, the next segment loses 4 cells (blank tape supplies them if there is none) and l = 4n + 5. So l plus the segments is 4m + 1 for 2^m sub-rounds (one round, what earlier notes called the fast counter), then m grows by 1. Checked against the machine one sub-round at a time: of the 300,000 sub-rounds after step 2,918 (12.6 million steps) the 299,954 regular ones all follow this; the other 46 are the transients of the first two rebuilds. The rules are now proved in Lean for all sizes (the claims below); this check of the machine stays as a test. (`holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/model.py` (`check 300000`))

**Computed (trusted C/Python)** — The binary expansion, checked on the machine: With digits ai = (bi − 2)/3, W removes the last digit a, adds 1 to the digit before it and appends a zeros; the sum of all digits plus their number never changes. A tail (..., q, a) becomes (..., q + a + 1) after exactly 2^a steps, so an interior with digits a1, ..., ak is a single block after exactly T = Σi 2^ai + ... + ak + k − i steps of W: the positions of the 1s in the binary expansion of T are the partial sums of the list read from the right. Checked on the machine: the model predicts single blocks at sub-rounds 1,616 and 261,907 of that run and both are there; W steps and counter steps taken many at once agree with the machine in 28 test jumps; and after the third rebuild the lists at seven ends of rounds, up to step 2.8·10^10, are those of a direct run of the machine (`3 2^25 14 2 8 2 14 | 85` at step 22,558,329,286, ..., `3 2^12 20 2^6 14 2 8 2 14 | 109` at step 28,107,393,382). (`holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/model.py` (`check 300000`, `partial`, `rounds`))

**Proved in Lean, kernel only** — Every sub-round of the regular kind, for all sizes: Five machine rules, each for every value of its parameters and every tape further out: `glong` (last interior block 3a + 2, last block b + 2: W on the interior, the last block becomes 1 and a new zone gap of b + 1), `gshort` (last block 1: the carry removes the leading gaps of 3, takes 4 cells from the next gap, which has at least 4, and sets the last block to 4n + 5), `gzero` (the carry meets two 1s side by side before a gap of at least 2: last block 4n + 4), and the two rebuild sub-rounds below. Put together (`subround`): at the moments the head is in C on a 0 right of a 1, a configuration `1^(3q) 0 [digits] 0 1^l C> [gaps]` with at least one digit goes in one sub-round to W of its digits and one step `gstep` of the counter, which is defined for every last block and every zone except at the *small gaps* (a carry meeting a gap of 1 or 2 cells, or two 1s side by side before a gap of 0 or 1). The rules are proved by `rfl` steps, the crossing lemmas and `omega`; the earlier observation that W and the counter do not influence each other is now a theorem. (`glong`, `gshort`, `gzero` in `lean/Subround.lean` (generated by `py/gen_subround.py`); `subround` in `lean/Collapse.lean`)

**Proved in Lean, kernel only** — The list is the binary expansion of the time it has left: With T(x :: r) = 2^x (1 + 2 T(r)) on the digits listed nearest the head first, W lowers T by exactly 1 and keeps the first block plus the digits plus their number (`T_W`, `mass_W`). So from any configuration of this shape the machine reaches the single block of 3 · mass cells after exactly T sub-rounds, the counter advanced T times, if the counter meets no small gap on the way (`collapse`; `advance` for fewer sub-rounds). A regular counter (last block 1 mod 4, every gap 3 mod 4: the binary counter of the picture) never meets one (`regular_total`), so from a regular configuration the collapse always happens, without a halt (`collapse_regular`). (`T_W`, `collapse`, `regular_total`, `collapse_regular`, `lean/Collapse.lean`)

**Proved in Lean, kernel only** — The rebuild sub-round, and why single blocks grow: A single block of 3(k + 1) cells with last block b + 5 becomes `3 2^k` with last block 5 and a new zone gap of b cells in front (`rebuild`, rule `single`); with last block 1 and a first gap of at least 2 it becomes `3 2^k` with last block 4 and the first gap 2 shorter (`rebuild_one`, rule `singleone`). The digits of `3 2^k` give T = 2^k − 1 and mass k + 1, so if the counter meets no small gap the single block comes back with the same 3(k + 1) cells after 2^k sub-rounds (`rebuild_cycle`). The single blocks of the run grow (36, 57, 90, ...) only because small gaps move cells of the counter into the list; the new gap a rebuild makes (b, a multiple of 4 when the last block is 1 mod 4) is where the first small gap comes from. (`rebuild`, `rebuild_one`, `rebuild_cycle`, `lean/Collapse.lean`)

**Proved in Lean, kernel only** — The run from blank tape through the first rebuild, to step 71,355: The kernel evaluates the first 2,918 steps (to `3 2 8 5 14 | 9`) and the counter `gstep`; the rest is the rules above: 1,616 sub-rounds to the single block of 36 cells (`first_single`), the rebuild sub-round (`first_rebuild`, step 70,871: `3 2^11 | 5`), and 13 more sub-rounds to step 71,355, where the carry meets a gap of 2 cells, the first sub-round of the run the rules do not cover (`first_uncovered`). (`reach_2918`, `first_single`, `first_rebuild`, `first_uncovered`, `lean/Run.lean`)

**Proved in Lean, kernel only** — Every sub-round, small gaps included: the pass machine: At every moment (the head in C on a 0, a last block l on its left, then any blocks of 1s separated by single 0s, and on its right any zone of gaps) the next sub-round is the same two sweeps. The left sweep (`start`) erases the last block, moves the block before it one cell to the right and adds 3 cells to the block before that. The right sweep reads the tape in one of three phases A, E, C (the machine states) with an *open block*, the 1s just left of the head. On a 1, A writes 0 (the open block closes, an empty one opens) and E and C keep it; the phase goes A, E, C, A. On a 0: C after a non-empty open block is the next moment (the open block is the new last block); C or E next to an empty open block fill two cells; E after an open block, and A on `010`, move the open block one cell right, add 3 to the block before it and start again in A; A on `000` writes `111` and goes on in C; A on `001` writes `101` (the open block closes at the middle cell); A on `011` halts. Each move is a machine rule proved for every size (`lean/Pass.lean`, generated by `py/gen_pass.py`); `pstep` puts them into one total function, and `sub_moment` and `sub_halt` prove that a sub-round it computes is a run of the machine with exactly its number of steps, and that a halt it finds is a halt of the machine. So the halts of the machine are exactly the carries that meet `011` in phase A. W on the list and the binary counter (the rules above) are the cases where the right sweep only meets blocks 2 mod 3 and gaps 3 mod 4; the small gaps are the moves A on `001` and `010`, which move cells of the counter into the list. (`pstep_next`, `pstep_done`, `pstep_halt`, `sub_moment`, `sub_halt`, `subs_moment` in `lean/General.lean`; the moves in `lean/Pass.lean`)

**Proved in Lean, kernel only** — The run from blank tape through two transients, to the third single block: From step 71,355 (where the first small gap was the end of the proved run) the kernel evaluates the pass machine: 7 sub-rounds of the first transient to the regular configuration `3 2^6 11 5^2 2^2 5 | 5` with zone gaps 4 7 3 (`first_transient`); `collapse`, with the counter evaluated by the kernel (260,270 counter steps), gives the second single block, 57 cells (`second_single`); `rebuild` and 24 more sub-rounds of the pass machine give `3 2^13 11 5^2 2^2 5 2^2 5 | 9`, a regular configuration (`second_transient`); and `collapse_regular` the third single block, 90 cells, 536,840,942 sub-rounds later, with a regular counter (`third_single`). Direct simulation puts that block at step 22,558,329,283; the Lean proof does not evaluate any machine step past step 2,918, and the counter after the third block is left existential (it needs the counter in closed form). (`first_transient`, `second_single`, `second_transient`, `third_single`, `lean/Transient.lean`)

**Proved in Lean, kernel only** — The run from blank tape to rebuild 40: Two lemmas make the counter and the list cheap for the kernel at any size. Scaling (`giter_scale`): with 4j more cells in the last block, one step of the counter takes exactly 2^j steps, so `gfast` advances the counter by N steps in about two jumps per binary digit of N (`gfast_sound`). Part of a collapse (`advance_to`): W lowers the time left T by one and keeps the mass, and T is one to one (the list is the binary expansion of T), so after M sub-rounds the digits are the only list D′ with T(D′) + M = T(D); no step of W is evaluated. From the third single block the run is then a chain of 454 segments (`lean/Chain.lean`, generated by `py/gen_chain.py 40`): 227 *advances*, W and the counter for as many sub-rounds as the counter makes before it meets a small gap of the zone (up to about 2^1,160 at once), and 227 *passes*, 1 to 3 sub-rounds of the pass machine evaluated by the kernel where the counter is stuck (a small gap, or a single block and its rebuild). `single_40`: the run from blank tape reaches the single block of rebuild 40, 3,483 cells, after more than 2^1,160 sub-rounds (so more than 10^349 machine steps), and does not halt before it. The single blocks of rebuilds 4 to 40 are those of the hybrid run of `py/model.py`. (`single_40`, `lean/Chain.lean` (generated by `py/gen_chain.py 40`); `advance_to`, `T_inj`, `lean/Advance.lean`; `giter_scale`, `gfast_sound`, `lean/Counter.lean`)

**Computed (trusted C/Python)** — What the regular rules leave, and the pass machine against the run: Before the pass machine: the hybrid run of `py/model.py` through 243 rebuilds with every directly simulated sub-round checked against the regular rules (`c/rules_check.c`): of 70,055 sub-rounds simulated directly in the transients, 67,154 follow a regular rule with its exact step count and none differs; 2,901 are not covered, 1,584 where the carry meets a small gap and 1,317 where cells the small gaps moved into the list leave a last block that is not 2 mod 3. The pass machine covers all of them. Its Python mirror `py/passm.py`, move for move the Lean function, agrees with the machine on 30,000 random tapes (configuration, step count and halts) and, in the hybrid run through 243 rebuilds, gives for every one of the 24,034 stretches the run simulates cell by cell (the transients and the sub-rounds where the counter reaches an irregular gap; 363,515,147 machine steps) exactly the configuration and step count of `c/trans.c`. (`py/rules_check.py`, `c/rules_check.c`; `py/passm.py` (`check 30000`, `hybrid 243`))

**Computed (trusted C/Python)** — Tapes of the same shape that halt: A rebuild starts when the interior is a single block. The tape 1^3k 0 1^4k−3 with the head in C on the 0 right of it, a single block of 3k cells meeting the counter exactly at the start of round k − 1, halts for every k from 3 to 9 (after 311, 659, 1,343, 2,699, 5,399, 10,787 and 21,551 steps; direct simulation). So no property of the shape alone can show that the machine never halts: it depends on which single blocks and counter values the run from blank tape produces. (`holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/model.py` (`halting 9`), `c/trans.c`)

**Heuristic / observed** — 986 rebuilds without a halt: A run that takes the regular sub-rounds by arithmetic (any number at once, with the two rules above) and gives everything else to the machine itself, cell by cell: the transient after each single block, and the sub-rounds where the counter reaches an irregular gap of the zone. It passes 986 rebuilds; by then the counter has made more than 2^105,958 sub-rounds, so the machine more than 10^31,896 steps, and the single block has 317,877 cells. A halt could only be found by the direct part and none was. The sub-rounds the arithmetic part takes are of the kinds proved in Lean for all sizes (W and the regular counter); the direct part is now covered by the pass machine as well (proved for every sub-round); what rests on Python is the arithmetic that takes many regular sub-rounds at once (`applyW`, `enc`/`dec`); through rebuild 40 that arithmetic is now proved too (above). The small gaps never hold the counter for long: in the segments of `py/gen_chain.py` through rebuild 200 (single block 54,075 cells), each of the 1,410 places where the counter is stuck is cleared by 1, 2 or 3 sub-rounds of the pass machine (403, 933 and 74 times). (`holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/model.py` (`run 986`), `c/trans.c`)

**Open** — Does it halt from blank tape?: Not known. Every sub-round is proved, with its exact step count, and the only halting move is a carry that meets `011` in phase A (a gap of one cell followed by two 1s side by side). Tapes of the same shape do halt that way (the halting family above ends with the zone `... 3 3 1 0`). So the question is arithmetic: whether the single blocks and counters that this run produces ever lead a carry to such a place. The halting family needs the single block to arrive exactly when a round of the counter starts, a coincidence of two binary numbers that the run has avoided so far. In Lean the run is proved to rebuild 40 (more than 10^349 steps); each further rebuild costs the kernel a few more segments, so the proved run can be pushed further, but a proof for all rebuilds needs a rule for the counter at the moment the single block arrives.

## For later

1. Lean: push the chain further (`py/gen_chain.py R`; 40 rebuilds take the kernel about 3 minutes, growing with the
   length of the lists), or better a rule for where the counter stands when a single block arrives.
2. The transient as a map: with the pass machine, show that a transient depends only on the last block and a bounded
   prefix of the zone once the single block is large, so that a rebuild is an explicit map on (single block, counter),
   and the halting question becomes whether that map ever leads a carry to `011` in phase A.
3. The same skeleton appears in `1RB0RF_1RC1LB_1LD1RE_1LB0LD_1RF0RC_1RA---` (blocks 2a + 1, last block a multiple
   of 5) and probably in `1RB0RE_1LC0RA_1RE1LD_0LB0LF_1RA1RA_0LD---`; their sub-rounds may be sweep machines as well.

## Reproduce

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE--- 30000000000 at C R 400      # 2 minutes; the round ends that py/model.py rounds compares with
gcc -O2 -o triage tools/c/triage.c && ./triage 1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE--- 1000000000
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/model.py check 300000     # machine against model, sub-round by sub-round
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/model.py partial          # jumps of many sub-rounds against the machine
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/model.py rounds           # round ends after the third rebuild against the direct run
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/model.py halting 9        # the halting tapes 1^(3k) 0 1^(4k-3) C>0
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/model.py run 986          # the hybrid run (87 minutes; run 243 takes 5)
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/gen_subround.py > lean/Subround.lean   # the Lean rules
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/rules_check.py 243      # 8 minutes: the regular rules against every directly simulated sub-round
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/gen_pass.py > lean/Pass.lean      # the moves of the pass machine
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/passm.py check 30000     # the pass machine against the machine, random tapes
python3 holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/py/passm.py hybrid 243      # 6 minutes: against every directly simulated stretch of the hybrid run
```

Pages: [`explainer.html`](../../pages/holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/explainer.html), [`proof-status.html`](../../pages/holdouts/1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---/proof-status.html).
