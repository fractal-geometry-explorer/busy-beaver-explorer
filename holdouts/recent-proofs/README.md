# What the proofs of 17 to 19 November 2026 teach

Between 17 and 19 November 2026, busycoq pull requests 78 to 109 decided 32 of the 608 holdouts: 29 by Alex Havrilla
of DeepMind (PRs 78 to 97 and 103 to 107), and three by our own retargeting of DeepMind's PR 93 engine (PRs 108 and
109, and PR 100 by valu42). All were compiled here (see `holdouts/external.json`). Each machine's explainer page now
opens with a plain-language section, "How the proof works". This folder keeps the technical side:

- [`techniques/`](techniques/): one note per group of proofs. It gives each proof's invariant, encoding, macro steps,
  what `vm_compute` decides and how big it is, what another machine would need for the same method, and candidate
  open holdouts.
- [`followup/`](followup/): four attempts to use the methods on open holdouts. Each lists what was tried and the
  evidence level of each result. None decided a machine.

**Update, 25 November 2026:** busycoq PRs 110 to 119 (23 to 25 November) use a newer method: recursive sweeps with a
small carry. See [`recursive-sweeps-nov23-25.md`](recursive-sweeps-nov23-25.md). It covers each proof, a comparison
with our folders, and a screen of the open holdouts for transfer (script in [`tools/`](tools/)).

**Survey, 26 November 2026:** [`technique-survey-nov26.md`](technique-survey-nov26.md) classifies every technique
that has decided a holdout, lists what failed and on which machines, and ranks eight new techniques to try.

**Halt hunts, 26 November 2026:** [`halt-hunt-ranking-nov26.md`](halt-hunt-ranking-nov26.md) estimates the expected
number of halts per doubling of the run for eight machines with proved visit maps, calibrated on the one that
halted, and ranks the hunts. The replay tool it uses is [`tools/segreplay`](../../tools/segreplay/README.md).

**Invariant transfer, 26 November 2026:** [`followup/invariant-transfer.md`](followup/invariant-transfer.md) tests
technique D of the survey. The invariants of 236,071 proved tables were tried on the 509 open holdouts in three
screens (same table at another start, transitions that go quiet, lockstep runs of 2,138 neighbour pairs). Nothing was
decided; four pairs give reductions of the form "the holdout cannot halt before one local context occurs". Tools and
data are in [`tools/transfer/`](tools/transfer/).

**Carry screen, 26 November 2026:** [`followup/lap-carry-transducers.md`](followup/lap-carry-transducers.md) tries
proposal C of the survey. A sweep's carry is its crossing sequence, so it needs no learning; a screen of all 608
finds two open machines with a small exact carry over full sweeps, and a closure checker that closes on none of
them. Nothing was decided.

**Cryptids pull request 42, 27 November 2026:** [`cryptids-pr42-nov27.md`](cryptids-pr42-nov27.md) reads the two new
Lean proofs (1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE and 1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF), compares the
11 ported proofs with their Rocq twins, and screens the 501 open holdouts for the two signatures the new proofs rest
on (a finite end controller beside a write-only bulk; an exact run grammar with return shapes). Nothing was decided.

**Write-only test, 27 November 2026:** [`followup/write-only-test.md`](followup/write-only-test.md) tests the
write-only property of cryptids pull request 42 directly, on the 12 end-controller candidates and then on all 501
open holdouts, at one end and at every boundary of the tape. Five candidates fail, one fails on one end word, six
pass for a reason that gives no proof. A decider built on K-cell call summaries fails on both proved machines; the
note says what classes of half tapes it would need. Nothing was decided. Tools: [`tools/writeonly/`](tools/writeonly/).

## The methods, in short

| method | proofs | what it needs |
|---|---|---|
| Fast engine on run-length tapes of macro words, each rule proved sound, run to the halt | PR 82, 84, 93, 100, 108, 109 | a halting run that the engine can reach (2.5 million engine steps for PR 93) |
| Lap on linear forms: after an exact run with binary counts, one lap maps C(N, m) to C(aN + b·s(m) + cm + d, m + k), and every branch is decided the same way under a band invariant | PR 78, 79, 80, 86, 95 | a run that settles into a lap of fixed shape |
| Wall of capacity m: only parities and one inequality are tracked, never the exact Collatz-like orbit | PR 97 | a parity grammar closed under the step, with no halting branch |
| Odometer jumps: b^k counter ticks in one operation, then an exact executor to the halt | PR 83, 89 | closed-form drains, and a carry grammar |
| Memoised left contexts: a reflecting crystal wall plus tables of half-tape summaries, and in PR 91 a tower of 14 walls | PR 88, 91 | few reachable contexts at each layer |
| Token simulators with a crystal and an arbitrary carried word, hub maps such as n = 2m + p going to 3m + q, fuel queues | PR 85, 87, 90, 94, 96, 104 | a hub map that is total, or a fuel inequality |
| Stack and potential certificates | PR 81, 92, 103, 105, 106, 107 | a finite table of cases plus a linear potential |

The nine engine machines are four tables (P, Q, T3 and T4), each started in different states.

## Follow-up on open holdouts (19 November 2026)

Nothing was decided. These results are computed (exact accelerated runs checked against direct simulation), not proved.

- **T4-engine variants** ([`followup/t4-variants.md`](followup/t4-variants.md)):
  - 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF and 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF are one table, started in A and (mirrored) in C. That table is PR 93's T3 with E and F merged and the PR 109 detour. All of PR 93's rules hold for it, and a Coq proof skeleton compiles in 65 s, missing only the final evaluation.
  - The engine ran to fast step 10.97 million and 15.36 million with no halt; T3's own halt comes at 2.45 million.
  - For 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF and 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE, the rules the change breaks have no local restatement that fits the engine.
- **PR 97 walls** ([`followup/wall-capacity.md`](followup/wall-capacity.md)):
  - For 1RB1RA_1LC0RB_1LD0LB_1RA0LE_---1LF_1LB0LA, a parity-only invariant cannot work. With free residues, a halting chain of 60 phases exists, and the configuration `1^14 0^z B>0` with z = 2082616591761832409 halts after about 4.4·10^57 steps. The run from blank tape starts the same shape with z = 11.
  - For 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC, no halt was found among 5,360 walls up to 200 cells. The parity abstraction does not close.
- **PR 78 laps** ([`followup/attractor-lap.md`](followup/attractor-lap.md)):
  - An exact word simulator with symbolic counts records every branch condition.
  - 1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC has a three-level orbit: highway, era map C(L) to C(L+2), and regimes with K = 2^(8+r) + 5. The branch path changes every era, so no fixed lap exists.
  - 1RB0LC_1LC0RE_1LD1LB_1LA1LD_1RF0RA_---1RE and 1RB0LD_1RC0RF_0LD0LE_1RF1LC_0LB1LE_0RA--- are growing counters with no fixed-shape hub.
- **Summary certificates, finite-state version** ([`followup/rlepds-nov26.md`](followup/rlepds-nov26.md)), technique B of the
  survey: `tools/c/rlepds.cpp` decides none of the 509 open holdouts; the note says why cryptids PR 37's round is out of reach.
- **PR 42 return shapes** ([`followup/return-shape.md`](followup/return-shape.md)), no closure: an automatic
  version of the PR 42 proof shape closes on that machine in a second and on none of the 501 open holdouts.
- **PR 89 odometers** ([`followup/odometer.md`](followup/odometer.md)), no halt reached:
  - 1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RE--- to 1.6·10^712 steps;
  - 1RB1LF_1RC0RA_0RD1RA_1RE1LA_0LA---_1RF0LD to 1.2·10^1572 steps (closest approach: an empty block next to a block of 49 copies);
  - 1RB1LF_1LC0RD_0LD0LC_1RE0LA_0RA0RC_0RE--- to 1.4·10^515 steps. That machine is the F05 core table with E1 = 1RF and F0 = 0LD, mirrored and started in E, and it halts exactly when E reads 1 with a 1 on its right.
  - 1RB0LC_0RC0RB_1LD0RE_0LE0LB_1LA1RF_0LD---, the same table started in A, ran to 1.6·10^522 steps.

The scripts behind the follow-up are kept in the project's shared files, not in this repository.
