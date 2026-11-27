# What cryptids pull request 42 teaches (27 November 2026)

On 26 November 2026 Tom Zahavy (DeepMind) opened pull request 42 on `google-deepmind/cryptids` (head `84c3ef8`). It
adds 13 Lean proofs about BB(6) holdouts. We compiled all 13 here (our PR #632; Lean v4.35.0-rc4, axioms `propext`,
`Classical.choice` and `Quot.sound` only, no `sorry`, no `native_decide`). Two decide machines that nobody had decided
before, and 11 are Lean versions of proofs that already exist in Rocq as busycoq pull requests 64, 88, 91 and 112 to
119. This note reads the two new proofs closely, compares the 11 others with their Rocq twins, and asks which open
holdouts the ideas fit. It builds on [`recursive-sweeps-nov23-25.md`](recursive-sweeps-nov23-25.md), which covers
busycoq PRs 110 to 119.

Everything in the sections "Screen" and "Follow-up attempts" is computed, not proved.

## The short version

- **Both new proofs are recursive-sweep proofs**, the method of busycoq PRs 112 to 119: read the tape as a list of
  tokens, treat a trip into the list as a call that returns, state what the *front* of the list looks like on return,
  and close everything with an induction on a step budget. Neither proof writes down a closed set of whole tapes.
- **Each adds one idea that the earlier proofs did not have.**
  - 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE: the far side of the tape is *write-only*. A trip into it returns one
    bit, and that bit is already known when the trip starts (a parity of ones next to the head). So the near end is
    a finite machine by itself: 132 exact end words. The irregular bulk is never described beyond a 7-state automaton.
  - 1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF: the *whole* tape at each left turn belongs to an exact grammar over
    run lengths (5 nonterminals, runs of ones of length at most 11). What we called a chaotic engine at the right end
    is just the part of the grammar where the choices are. A call into a tail returns in one of 3 or 9 listed shapes.
- **Our own work on both machines stopped at the same place**: we split the tape into a regular part and an irregular
  part by *position*, and then looked for a closed language of raw cells. The proofs split by *call depth* instead.
- **The Lean ports are much shorter than the Rocq files where a library is shared**: the five machines of busycoq
  PRs 115 to 119 take 200 to 554 lines each in Lean, on top of two shared modules, against 6,985 to 7,994 lines each
  in Rocq. For the three halting proofs Rocq's `vm_compute` is about ten times faster than Lean's kernel.
- **For our open holdouts** a screen of all 501 for the two signatures finds that the loose form of each is common (about
  half of all tape ends), so it does not rank machines by itself. A strict form that copies the two proved machines
  leaves 12 and 10 candidates; one of them was already the best candidate of the wall-carry screen of 26 November.

## 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE: a finite end controller beside a write-only bulk

File `BusyBeaver/BB6/NonHalt/M_1RB0LD_1LC0RE_HHH1LD_1LE1LA_1RA0LF_1LC1RE.lean`, 3,067 lines (about 1,200 of them are two
data tables), 26 s to build here.

**Tokens.** Right of the head the tape is a list over four tokens `r0 = 1`, `r1 = 01`, `r2 = 001`, `r3 = 0001`. Left
of the head it is a list over two tokens, `1` and `10` (read outward from the head).

**The macro machine.** Four modes: `mRA` and `mRAE` (state A moving right), `mLD1` and `mLD0` (state D moving left).
`stepMacro` is a function on (mode, k, left list, right list), where k counts ones just left of the head. Each case
is proved against the raw machine (`segmented_step_sound`). The invariant `ValidSeg` that this step preserves is
small:

- the left list never has two `10` tokens in a row (`validL`);
- the right list, read from its far end by a 7-state automaton (`dfaStep`, `evalR`), never reaches the reject state.
  The automaton forbids the factor `00001` and tracks a parity; each mode allows a few of its states.

That invariant does *not* exclude the halt. `stepLD0` returns `none` (the machine halts, C reads 0) exactly when the
head comes back in `mLD0` and the left list is the single token `10`. The rest of the proof shows this never happens.

**The conservation law** (`callRA_advances`). Take any valid `mRA` state with left list `L`, and let p be the number
of ones around the head: k plus the leading `r0` tokens of the right list. If p ≥ 2, then either the machine never
halts, or it comes back in mode `mLD0` with left list `L` if p is even and `1 :: L` if p is odd, and a right list of
one of three shapes (`GoodRetR`). Nothing else about the right list matters, and nothing else comes back. The proof
is a strong induction on the number of steps left before a halt (`callRA_advances_budget`): a trip to the right is
made of shorter trips of the same kind.

**The checkpoints.** Since a trip returns only a bit that is known at its start, the left end runs by itself. The
proof lists 132 exact left lists (`cpTree`; the longest has 35 tokens) and proves that from `mLD0` at any of
them, with any right list of the three shapes, the machine reaches `mLD0` at one of them again
(`cpInv_advances`). The check is a small verified program, `checkSym`: it runs the macro machine on an exact left
list and a right list that is an exact prefix plus a symbolic tail (a set of automaton states), branches where the
tail decides, and uses the conservation law as a single step wherever a trip starts. `checkSym_sound` is proved once
by induction on fuel; `decide +kernel` then evaluates it on the 132 checkpoints. The heading in the file calls the
result a "132-checkpoint period-87 CPS graph". 32 macro steps from the blank tape reach a checkpoint (`runMacro_32`).

**What we had.** Our folder describes "the alternating pattern 1010… with defects" and says "no regular word or
counter shows up". We proved the two fast moves and the halting route (`halt_route`: two steps before a halt the
tape reads `0 0 E>1`). Every decider we ran looked for a closed set of whole tapes over raw cells: n-gram CPS to
width 20, with position mod p, with side automata of up to 4 states, run-length windows, and a SAT search for
automata of up to 8 states per side. All failed.

**Why they failed, in hindsight.**

- The fact that carries the proof is a parity of a run of *unbounded* length (p above), compared across a trip of
  unbounded duration. A window cannot hold it, and "position mod 2" is not the same thing as "length of this run
  mod 2".
- The left-end words are up to 35 tokens (over 40 cells) long and must be known *exactly*. That is far more than an n-gram of
  width 20 or an automaton of 8 states holds, but it is cheap as a finite list.
- We never asked which side decides. A plain run shows it: this machine comes back to within 24 cells of its left
  end in only 94 different ways in 10^9 steps, and no new one appears after the first quarter of the run (the screen
  below). The right side keeps producing new words.

## 1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF: an exact grammar for the whole tape, with return shapes

File `BusyBeaver/BB6/NonHalt/M_1RB0RC_1LC0RB_1LD0LD_1RA1LE_HHH0LF_1LB1LF.lean`, 1,693 lines, 18 s to build here.

**Tokens.** The right side is a list of numbers; d stands for `1^d 0`. Two forms of configuration: `BR l m R` is
`l 0 1^m B> R` (the call: B enters R with a marker of m ones behind it) and `BL l R` is `l <B R` (the return).

**The grammar** (`Gram`). Five nonterminals over run lengths:

    ValidR     := 4 Post41 | 4 1 Post41
    Post41     := [3 5 1 1] | Post41Out
    Post41Out  := [3 6 5 1 1] | 3 Body2Tail | 5 Body2Tail | 6 RareTail | 8 RareTail
                  | 2 5 RareTail | 2 1 3 RareTail | 4 1 3 RareTail
    RareTail   := {6, 8}* ValidR
    Body2Tail  := {6, 8}* (RareTail | 9 RareTail | 11 RareTail | 5 5 RareTail | 5 1 3 RareTail | 7 1 3 RareTail
                  | [6 6 5 1 1])

At every left turn the whole tape is a `ValidR` list with the head on blank tape to its left. So the tape is a
regular language over nine run lengths (1, 2, 3, 4, 5, 6, 7, 8, 9, 11). The blank tape gets there after 3,884 steps
of an executable run-length machine (`stepM`, checked by `decide +kernel`), with a list of 41 runs.

**The contract** (`SafeRet N l c Q`): from c, either the machine is safe for N steps, or within N steps it reaches
`BL l R'` with `Q R'`. The left part `l` is arbitrary and comes back untouched, which is what lets calls nest. Three
statements are proved together by strong induction on N (`callR_main`):

- `PValid`: a call on a `ValidR` list with a marker of m ≥ 3 ones returns `(m − 2) :: 1 :: T` with `T` in `Post41Out`;
- `PRare`: a call on a `RareTail` list with marker 3 returns in one of 3 shapes (`RareRet`);
- `PBody2`: a call on a `Body2Tail` list with marker 3 returns in one of 9 shapes (`Body2Ret`).

Each return shape, with 3 added to its first run (`bumpR`), is again in the grammar (`bumpR_rareRet`,
`bumpR_body2Ret`). Four concrete rules (`rule_41`, `rule_43511`, `rule_436511`, `rule_66511`) are the base cases. One
outer cycle is two calls (`BL_valid_safe`). The halt (E reads 0) never needs to be mentioned: every case of every
contract has a next step.

**What we had.** Our README lists the run lengths at a left turn correctly
(`1^4 0 1^4 0 1^3 0 1^8 0 1^6 0 1^4 0 1 0 1^5 0 1^9 0 1^4 0 1 0 (1^5 0 1^6 0 1^4 0 1 0)^n …`), proves four sweep
rules, and then describes "a chaotic engine" of 450 to 610 cells at the right end beside a frozen archive. It ends:
"A proof of non-halting probably needs a description of the engine's states, which is not known."

**What the proof does differently.** It never separates archive and engine. The grammar holds for the whole list,
and a call simply recurses as deep as it needs. The "engine" is the part of the list where the most recent calls
returned; its width is unbounded in principle, which is why it "creeps up" in our measurements. The quantity that
is finite is the number of return shapes (3 and 9), not the width of anything.

A first check of how one could find such shapes by machine: take the run list at a late left turn, start a call
`0 1^3 B> R` on every suffix R, and record how the front of R is rewritten when the head comes back. The four most
frequent rewrites are the proof's own rules (`4 1 5 → 1 1 3 8` is `rule_41` with m = 3) and cover 361 of 740
suffixes. The rest are long, because most suffixes are not places where the real run makes a call. A learner has
to take its call points from the run.

## The 11 proofs that also exist in Rocq

Sizes are lines of the proof file; times are what we measured here (Rocq 8.20.1 on busycoq `33209bc`, Lean on
`84c3ef8`; the Lean time is for the proof's own module, after the shared modules are built).

| busycoq PR | machine | result | Rocq | Lean |
|---|---|---|---|---|
| 64 | 1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA | halts | 15,177 lines, 511 s | 7,373 lines, 154 s |
| 88 | 1RB0RD_1RC0LF_0LA0RB_1RE---_1LB1RA_0LE0LF | halts | 20,151 lines, 29 s | 19,456 lines, 266 s |
| 91 | 1RB1LD_1LC0RF_0RD0LB_1LB0LE_1LA---_0RA0RF | halts | 8,445 lines, 11 s | 7,878 lines, 113 s |
| 112 | 1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LF---_1LB1RF | never halts | 1,322 lines, 2 s | 1,438 lines, 15 s |
| 113 | 1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RC--- | never halts | 1,127 lines, 5 s | 1,170 lines, 11 s |
| 114 | 1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RC--- | never halts | 759 lines, 20 s | 964 lines, 7 s |
| 115 | 1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE | never halts | 6,985 lines, 90 s | 548 lines, 8 s |
| 116 | 1RB1LD_1RC0LA_1LA0RE_1LB1LA_1RF0RB_---0LB | never halts | 7,984 lines, 95 s | 289 lines, 4 s |
| 117 | 1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA | never halts | 7,994 lines, 97 s | 440 lines, 4 s |
| 118 | 1RB1RF_1LC0RF_1LE0LD_1RC0LB_---1RA_1LB1RA | never halts | 6,985 lines, 81 s | 554 lines, 8 s |
| 119 | 1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC | never halts | 7,982 lines, 94 s | 200 lines, 3 s |

What the comparison shows:

- **Same proofs, same shape.** The Lean files follow the Rocq ones definition by definition (`Q5`, `InL`, `potBits`
  and `BoxCPS` for 113; the 10-state pair automaton and the 14 + 4 contracts for 112; the tower of walls for 91).
  No port changes the mathematics.
- **The shared core is finally shared.** Our earlier note found about 6,100 identical lines between the Rocq files
  of 115 and 116. In Lean these are two modules: `Calculi/PairStackA.lean` (8,823 lines: the sweep relations `BigF`
  and `BigD1` and the invariant library) and `Calculi/PairStackB.lean` (2,202 lines: the 6-mode machine `tm484`, its
  bisimulation with the sweep relation, and the closed wall predicate `W_closed`). A machine's own file then only
  maps its table onto the core and runs a short prefix to the entry point (174 steps for 119, whose whole file is
  200 lines). 115 and 118 import only the first module.
- **The budget calculus is a small library.** `Calculi/Excursion.lean` holds `HaltsIn`, `Leads` and `Advances`
  ("if c halts in n steps, it first reaches a P-configuration that halts in fewer"), ported from busycoq's
  `Queue_v1.v`. Both new proofs and most ports use it or a local copy (`safe`, `SafeRet`).
- **Kernel evaluation is the bottleneck in Lean.** The halting proofs 88 and 91 replay long accelerated runs. Rocq
  does it with `vm_compute` in 29 s and 11 s; Lean has no trusted equivalent short of `native_decide`, so the ports
  pack their tables into literals and use `decide +kernel` (159 and 92 uses), and take 266 s and 113 s. Only 64 is
  faster in Lean; that port is half the length of the Rocq file and imports a run-window module
  (`Calculi/RunWin.lean`).

## How this differs from what we do

| | our folders and deciders | PR 42 (and busycoq 112 to 119) |
|---|---|---|
| unit of description | the whole tape at a turn, over raw cells or fixed words | a token list, cut where the machine itself turns |
| how the tape is divided | by position: frozen part, periodic part, irregular zone | by call depth: a call on a tail, with the rest of the tape as an untouched frame `l` |
| what the invariant fixes | a closed language of tapes | what a call returns (a few front shapes, one bit), plus one loose condition on the list |
| the irregular part | must be described, or the proof stops | left arbitrary within a small automaton or grammar |
| induction | on a closed set (CTL, CPS), or on a measure | on the step budget; a call may also never return, which counts as safe |
| computation | search tools outside the prover, then a certificate | a reflected checker proved once, then run by the kernel on a table |

Two habits of ours are worth changing. We filed both machines under "chaotic", one as "no structure found" and one
as "engine not understood", because the *tape* looked irregular; in both proofs the irregular part is real and stays
unexplained, and the proof is about the interface to it. And our searches fixed the abstraction first (window width,
automaton size) and then asked whether it closes; the proofs take the abstraction from the run (the end words that
occur, the shapes that return) and only then check closure.

## Screen: which open holdouts show the same two signatures

Tool: [`tools/endsig.c`](tools/endsig.c); raw output for the 501 open holdouts at 3·10^8 steps in
[`tools/endsig-screen-nov27.txt`](tools/endsig-screen-nov27.txt). Both signatures are read off a plain run, at each
end of the tape separately.

- **End controller (signature A).** Each time the head comes back within 24 cells of the last 1 at one end, after
  being more than 48 cells away, record the state and the cells between that end and the head. Count the distinct
  records after each quarter of the run.
- **Run grammar (signature B).** Each time the head stands at or beyond the last 1 at one end, cut the whole tape
  into maximal runs and collect the distinct triples of consecutive run lengths. Record the longest run of ones and
  of zeros.

**Controls** (10^9 steps). 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE: 94 end records at the left end, all present
after the first quarter, while the right end is at 257 and still growing. 1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF:
at left turns the runs of ones are at most 11 long, every run of zeros is a single 0, and the 55 triples are all
present after the first quarter. So both proofs' key facts are visible in a run before any proof exists. One thing
is *not* visible: the sequence of end records of the first control is not periodic (no period up to 50,000), because
the head also re-enters the end zone in the middle of trips. The checkpoint graph has branches.

**The loose signature is common.** Among the 1,002 tape ends of the 501 open holdouts, 514 have a saturated set of
end records (none new in the second half of the run, at least 500 returns) and 216 have a saturated set of run
triples. Counters, bouncers with a fixed wall and nested counters all pass. Saturation alone says only that an end
is regular, which we mostly knew.

**Strict form A**: 20 to 5,000 end records, all present after the first quarter, at least 1,000 returns, and the
*other* end irregular (at least 50 records, still growing in the second half). 27 ends pass. 15 of them have 256 or
more records and are counters whose low digits fill the window (groups G11 and G12). The other 12:

| machine | end | end records | other end's records by quarter | our group |
|---|---|---|---|---|
| 1RB0RF_0LC1LB_1RD1LA_1RE0LC_0RA1RD_---0RC | left | 20 | 100, 115, 119, 119 | G02 |
| 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF | right | 20 | 66, 74, 81, 90 | block list with halving counts |
| 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF | left | 24 | 320, 322, 420, 505 | G08 |
| 1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LA0LB | left | 25 | 321, 327, 336, 346 | G10 |
| 1RB1RA_1LC1LB_1RE0LD_1RA0LB_---0RF_1RC0RA | right | 25 | 313, 323, 323, 324 | G10 |
| 1RB0LE_1RC1RA_1RD0RF_1RE0RA_1LA1LD_1RA--- | left | 26 | 75, 77, 81, 82 | G08 |
| 1RB0RE_1LC---_0RA0LD_1LC1LD_1RF0LA_1RC1RE | right | 28 | 201, 230, 249, 274 | G09 |
| 1RB1LA_1LC0RE_---0LD_1LA0LF_1RA1RE_1LA0LB | left | 34 | 332, 335, 335, 340 | G10 |
| 1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA | left | 35 | 281, 281, 286, 286 | G13 |
| 1RB0LC_1LA1RD_1LA1LF_0RE---_1RA1RE_0RB0LA | left | 45 | 82, 82, 82, 84 | G08 |
| 1RB1RE_1LC0RA_---1LD_1LA0LF_0LB0LC_1RB0LB | left | 45 | 89, 93, 97, 102 | G09 |
| 1RB0LE_0RC0RD_1LC0RB_0RE1RD_1LF1LE_0LA--- | right | 61 | 320, 321, 332, 333 | G10 |

**Strict form B**: at least 500 end turns, runs of ones at most 16, runs of zeros at most 2, at least 30 triples all
present after the first quarter, and at most 5 end records (the head always arrives the same way). 10 ends pass:

| machine | end | longest runs (ones, zeros) | triples | our group |
|---|---|---|---|---|
| 1RB0LA_0RC1LF_0RD0LA_1LD0LE_1RB1LF_---1LA | right | 10, 1 | 60 | G08 |
| 1RB0LD_0RC1RA_1RD1RB_1RE1LE_1LF0LA_---1LA | right | 9, 1 | 56 | G08 |
| 1RB0LC_1LC0RE_1LD1LB_1LA1LD_1RF0RA_---1RE | left | 6, 2 | 55 | G01 |
| 1RB0RC_1LC0RB_1RE1LD_0LB0LF_---0RA_1LB1LD | right | 3, 2 | 51 | G09 |
| 1RB0LB_1RC1LE_1LD0RF_---1LB_0LA0LC_1LB1RA | left | 4, 2 | 49 | G08 |
| 1RB0RE_1LC0RA_0LD1LB_1LA1LF_0LB0RD_0LB--- | left | 15, 1 | 47 | G02 |
| 1RB1RF_1LC0LF_1RD0LB_0RA1RE_1RD---_0RC0LA | right | 15, 1 | 47 | two periodic regions |
| 1RB0LE_0RC0RA_1LD0LC_1LA0LB_1RA1LF_---0LC | right | 13, 1 | 46 | G05 |
| 1RB1LF_0RC1RC_1LD0RD_0LE0LA_1RA0LB_---1LD | left | 4, 1 | 38 | base-4 counter with timers |
| 1RB0LF_1RC0RB_0RD0RA_1RE1LE_1RF---_1LA1LF | left | 5, 2 | 31 | G10 |

1RB0LD_0RC1RA_1RD1RB_1RE1LE_1LF0LA_---1LA is the table that the wall-carry screen of 26 November picked as its best
candidate (see [`recursive-sweeps-nov23-25.md`](recursive-sweeps-nov23-25.md)); two unrelated screens now point at it.
1RB0RC_1LC0RB_1RE1LD_0LB0LF_---0RA_1LB1LD shares its first two states with the machine just proved.

These lists are leads, not results. Neither filter was tuned beyond the two controls, and a machine can pass for a
dull reason (a counter passes B whenever its digits are short runs).

## Follow-up attempts, in order

1. **Return-shape learner for run grammars** (new tool, then the 10 machines of strict form B). For a machine whose
   tape at an end turn is a list of bounded runs: find the call points in the run (state and marker behind the head
   when it enters the list), record for each call the pair (tail entered, front on return), and group tails by the
   set of return shapes they produce. The groups are the nonterminals; `Gram`, `RareRet` and `Body2Ret` of the new
   proof are exactly this. Closure is then a finite check: each shape, pushed back as the next call's input, must
   land in a known group. Test first that it recovers the 5 nonterminals and 3 + 9 shapes of
   1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF. Start with 1RB0LD_0RC1RA_1RD1RB_1RE1LE_1LF0LA_---1LA and
   1RB0RC_1LC0RB_1RE1LD_0LB0LF_---0RA_1LB1LD.
2. **End-controller check** (the 12 machines of strict form A). For each: list the end records exactly, extend each
   to the full end word up to the first place the bulk begins, and test the write-only property directly. Run every
   end word against many different bulks taken from the run and count the distinct end words that come back. If the
   answer is always one or two, with the choice readable from a few cells at the start of the trip, then the
   machine has a conservation law of the `callRA_advances` kind, and the proof is a table of checkpoints plus one
   lemma. Also record where pre-halt configurations can occur: the method needs the halt to be possible only at the
   regular end.
3. **A reflected checkpoint checker in our Lean library.** `checkSym` is about 80 lines with a 330-line soundness
   proof and is not specific to its machine apart from the macro step. A generic version over our run-length
   simulator (exact near side, far side an automaton state set, a slot for one call lemma) would let attempts 1 and
   2 end in a kernel-checked theorem instead of a computed table. Use `decide +kernel` on packed tables, as PR 42
   does; our `native_decide` results could be redone this way where the run is short enough.
4. **Budget calculus as a shared file.** Port `HaltsIn`, `Leads`, `Advances` and `SafeRet` (with `bind`) into
   `tools/lean`. Our Lean folders prove macro rules but have no way to say "this call returns or runs forever";
   every recursive-sweep proof needs it.
5. **Re-read the folders we labelled chaotic.** For the machines in the two tables above, add to each README which
   end is the regular one and how many end records it has, so that the next reader starts from the interface and
   not from the bulk.
