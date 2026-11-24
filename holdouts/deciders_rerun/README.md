# Standard deciders rerun on the 257 unfamilied holdouts (21 November 2026)

The 20 November regrouping ([`../FAMILIES.md`](../FAMILIES.md)) left 257 open holdouts in no family (the "rest of
F01 to F11"). This folder reruns the standard bbchallenge deciders on all 257 with limits well above the usual ones,
to clear any cheap case before more work goes into them.

**Result: none of the 257 was decided.** Nothing new needed a Lean or busycoq certificate. (Any success would have
been easy to certify: busycoq has verified `verify_cycler`, translated cyclers and `verify_backwards` for any
number of states.) Per machine: [`results.json`](results.json); the same table is on the
[deciders page](../../pages/deciders.html#rerun) (source `pages/src/deciders/page.html`).

| decider | program | limits | outcome |
|---|---|---|---|
| cyclers and translated cyclers | `tools/c/tcyc.c` | 2·10^9 steps from blank tape; each record configuration compared with the last 4,000 on its side (up to 2,048 cells behind the head) | no repeat on any machine |
| backward reasoning | `tools/c/bkr.c` (DFS), `tools/c/bkr2.cpp` (by depth, with duplicates merged) | depth 3,000, 2·10^8 nodes | 249: a backward chain of 3,000 steps exists, so no depth up to 3,000 works. 8: the frontier grows exponentially, and a backward chain of 20,000 steps exists for each (rerun of 24 November, below) |
| n-gram CPS | `tools/c/ngramcps.c` via `ngsweep.py` | plain up to 30 cells per side; history 1, 2, 3 up to 20, 15, 11; LRU up to 11; asymmetric left 1..12 × right up to 16; 8·10^6 configurations or 40 s per run | every mode reaches a halting configuration at every width tried until the budget runs out |
| RepWL | `tools/c/repwl.cpp` via `rwsweep.sh` | block length 1..12, 14, 16, 20, 24, 28, 32, 40, 48 × threshold 2, 3, 4; 300,000 configurations (Coq-BB5 used 150,001), 2,000 steps per block above length 16 | 3,076 of 15,420 runs reach a halting configuration, the rest hit the budget |

What "fail" means differs: a run that reaches a halting configuration (`UNKNOWN`, "halt reached") is a genuine
failure of the decider at that setting, since its abstraction allows a halt; a run that stops at the budget
(`LIMIT`, `TIMEOUT`) only shows that the setting is too expensive. For n-gram CPS the plain decider reached a halt at
width 30 on 79 machines and ran out of budget earlier on the rest. The holdouts were already defined as the machines
these deciders fail on at bbchallenge's own limits; this rerun only confirms that larger limits don't change that.

Not rerun: FAR and weighted FAR (the SAT search of 16 November already rules out two-automaton invariants up to 11
DFA states per side for 513 machines, `../satctl.json`), and the bouncer decider (no implementation here; most of the
257 grow like a square root or slower, but they were already rejected by bbchallenge's bouncer decider).

## Backward reasoning with a bigger budget (24 November 2026)

The 8 machines whose backward search stopped at the budget rather than failing were rerun. Result: backward reasoning
cannot decide any of them at any depth up to 20,000, so no bigger budget will help.

- By depth with duplicates merged (`tools/c/bkr2.cpp`, compact rewrite), for 1RB0RE_1LC0RA_0LD1LB_1LA1LF_0LB0RD_0LB---:
  the number of distinct backward stencils at depth 10, 30, 50, 60, 70 is 22; 5,357; 1,047,348; 14,645,364;
  205,186,680, a steady factor of about 1.31 per step with no sign of dying out (stopped at 16 GB of memory).
  A stencil records exactly the cells the forward run reads, so two stencils at one depth never subsume each other:
  merging cannot shrink this count.
- `tools/c/bkr_beam.cpp` keeps 200 random stencils per depth and found, for each of the 8, a tape window from which
  the machine runs exactly 20,000 steps and halts without the head leaving the window. Such a chain means some
  backward branch survives to depth 20,000, so the decider fails at every depth up to there. The windows are in
  [`backward_chains/`](backward_chains/); `python3 holdouts/deciders_rerun/backward_chains/check.py` replays each one forward.

## The new programs, and how they were checked

- `repwl.cpp`: Repeated Word List after Coq-BB5. The head sits between blocks of L cells; each side is a stack of
  (word, count) with counts 1..T-1 exact or "at least T". Popping "at least T" branches into "at least T" and
  "exactly T-1" left. A block is simulated until the head leaves it; for L up to 16 a block run longer than
  6·L·2^L steps is a loop inside the block (that branch never halts), above 16 a run over the step cap is a failure.
  Zero words next to the blank end merge into it.
- `tcyc.c`: at each new record on a side, compare the cells behind the head, as far back as the head went since an
  earlier record in the same state, with that record's snapshot.
- `bkr.c`, `bkr2.cpp`: busycoq's `has_contra`: every chain of n reverse steps from a halting stencil dies.

Soundness test on random machines (two to five states, about 10% halting transitions): RepWL decided 132 of 230
machines and the translated-cycler test 1,091 of 1,500, and none of them halts within 2·10^6 (RepWL) or 3·10^6
(cyclers) steps. These tests are not in CI; they were run once (scripts in the session notes, outside the repo).

## Rerunning

```sh
gcc -O2 -I tools/c -o ngramcps tools/c/ngramcps.c; g++ -O2 -I tools/c -o repwl tools/c/repwl.cpp
gcc -O2 -I tools/c -o tcyc tools/c/tcyc.c; gcc -O2 -I tools/c -o bkr tools/c/bkr.c
./tcyc MACHINE 2000000000; ./bkr MACHINE 3000 200000000; ./repwl MACHINE L T 300000 2000
python3 holdouts/deciders_rerun/ngsweep.py machines.txt ng.jsonl     # NGRAMCPS=./ngramcps
bash holdouts/deciders_rerun/rwsweep.sh MACHINE                      # from the folder holding ./repwl
python3 holdouts/deciders_rerun/summarize.py RAWDIR                  # results.json from the raw outputs
python3 holdouts/deciders_rerun/build_page_section.py && python3 pages/src/deciders/build.py   # the page section
```

The run took about 4 hours on 4 cores. The raw outputs (n-gram logs per width, 340 KB compressed) are kept outside
the repository.
