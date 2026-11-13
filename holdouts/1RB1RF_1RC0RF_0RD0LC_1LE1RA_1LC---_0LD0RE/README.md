# 1RB1RF_1RC0RF_0RD0LC_1LE1RA_1LC---_0LD0RE

Nobody knows whether this six-state, two-symbol Turing machine halts when started on a blank tape: it is one of the holdouts left open by the bbchallenge project. It has a twin that behaves the same way step for step, up to a fixed delay. This page lists what is established, sorted by what each result rests on; the macro structure is not yet found.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RF |
| B | 1RC | 0RF |
| C | 0RD | 0LC |
| D | 1LE | 1RA |
| E | 1LC | --- |
| F | 0LD | 0RE |

**Verdict.** **The question is open, and the machine is not yet understood.** It halts only when E reads a 1, which never happened in 2·10^10 steps. Its twin (3a `..._0LD0RE`, 3b `..._1RB0RE`) does the same thing whenever F reads a 0 with a 1 on its left (Lean), and that is the only way F has read a 0 in every run, so the two machines very probably halt or run forever together.

## What it does

Twin of 3b `1RB1RF_1RC0RF_0RD0LC_1LE1RA_1LC---_1RB0RE`; they differ only in F0 (3a: 0LD, 3b: 1RB). From `L 1 F>0 R` both
reach `L 1 1 B> R` (3a in three steps through D1 = 1RA and A0 = 1RB, 3b in one; proved in Lean), so as long as F
reads a 0 only after a 1 (true in every run so far) they make the same run, 3a two steps slower per F0.

The machine halts only when E reads a 1; E has only read 0s. The tape is made of the words `1^2 0^2`, `1^2 0^3`,
`1^2 0`, `1 0^3`. The right end grows in bursts where each new cell costs about 4 times the previous one; the head
revisits the left end in groups of three at irregular times (3a: 606; 10,065; 231,515; 1,173,873; 301,884,839).
The macro structure has not been found. The family's scripts are in `holdouts/1RB1RF_1RC0RF_0RD0LC_1LE1RA_1LC---_0LD0RE/`.

## What is established

**Proved in Lean, kernel only:**

- **The halting configurations.** The machine stops exactly when it reads the symbol of a halting transition (E1); the generated statement covers every configuration. (`step_none_iff`, `lean/Blank.lean`)
- **No halt in the first 10,000 steps.** The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel. (`blank_runs_kernel`, `lean/Blank.lean`)
- **The twins agree on F0 after a 1.** From `L 1 F>0 R` both machines reach `L 1 1 B> R` (3a in three steps through D and A, 3b in one): `f0_after_1`. All other transitions of the two machines are the same, so a run in which F reads a 0 only after a 1 is the same run in both machines, 3a taking two extra steps per F0. (`lean/Rules.lean`, `holdouts/1RB1RF_1RC0RF_0RD0LC_1LE1RA_1LC---_0LD0RE/py/gen_rules.py`)
- **Shift rules.** Five shift rules for all n and any surrounding tape, e.g. B crosses `(1100)^n` leaving `(0011)^n`, D crosses `(11000)^n` leaving `(11110)^n`. (`lean/Rules.lean`)

**Proved in Lean with `native_decide`:**

- **No halt in the first 10^7 steps.** The same run, evaluated by compiled code. (`blank_runs_native`, `lean/Blank.lean`)

**Trusted computation (C/Python, not Lean):**

- **No halt in the first 10^9 steps.** The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 324 cells have been visited and 193 of them hold a 1. (`holdouts/triage.json`)
- **No halt in the first 2·10^10 steps.** Direct simulation with `tools/c/tmrun.c`. (`tmrun 1RB1RF_1RC0RF_0RD0LC_1LE1RA_1LC---_0LD0RE 20000000000`)
- **F reads a 0 only after a 1.** In the first 10^9 steps of both machines every F0 has a 1 on its left, and every time B reads a 1 the next cell is a 1 too (so F, entered from B, reads a 1). E always reads a 0. Not proved for the whole run: it would need an invariant of the tape (a CTL proof). (`holdouts/1RB1RF_1RC0RF_0RD0LC_1LE1RA_1LC---_0LD0RE/c/ctx.c`)

**Heuristic:**

- **Growth shape: exp/fixed.** Left of the start, the visited part of the tape stopped growing in the second half of the run (bounded so far, or growing so slowly that no record fell in the last half). Right of the start it grows like the logarithm of the step count: each new cell costs a roughly constant factor more time, the signature of a *counter* or of a Collatz-like map whose values are written on the tape (fitted exponent 0.072). (`tools/py/bbtools/triage.py`)
- **Growth.** The right end grows in bursts in which each new cell costs about four times as long as the one before (3a: cells 296 to 320 between steps 3.1·10^8 and 9.2·10^8); the head comes back to the left end in groups of three visits at irregular times (3a: 606; 10,065; 231,515; 1,173,873; 301,884,839). The tape is made of the words `1^2 0^2`, `1^2 0^3`, `1^2 0`, `1 0^3`.

**Open:**

- **Does it halt from blank tape?** Not known. No macro description of the run is known yet.

## Reproduce

From the repository root:

```
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB1RF_1RC0RF_0RD0LC_1LE1RA_1LC---_0LD0RE/lean/check.sh
python3 holdouts/1RB1RF_1RC0RF_0RD0LC_1LE1RA_1LC---_0LD0RE/py/gen_rules.py 1RB1RF_1RC0RF_0RD0LC_1LE1RA_1LC---_0LD0RE H162010 | diff - holdouts/1RB1RF_1RC0RF_0RD0LC_1LE1RA_1LC---_0LD0RE/lean/Rules.lean
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB1RF_1RC0RF_0RD0LC_1LE1RA_1LC---_0LD0RE 20000000000
```

## For later

More than a day's work remains: identify the configurations at the left-end visits and the map between them (the
irregular return times suggest a Collatz-like map), and prove the invariant "F reads a 0 only after a 1" (e.g. with a
CTL certificate) to make 3a ⇔ 3b a theorem.

Round 3 (not a result): the twin invariant was tried as a window CTL of the seven-state machine
`1RB1RF_1RC0RG_0RD0LC_1LE1RA_1LC---_1RB0RE_---0RE` (3b with F split into "F entered from B1", which halts on 0).
`bbtools.ctl` finds closed sets for K ≤ 7 but all of them allow that halt, and for K = 8, 9, 10 the search does not
close within its round limit. The bad event needs `B> 1 0`, i.e. a factor `1 0 1 0` met by the right-moving states;
in 3·10^8 steps the tape right of the head is made of `1 0^2`, `1 0^3`, `1^2 0^2`, `1^2 0^3` (no `1 0 1` factor)
except next to the head, so a hand-made CTL whose right automaton is that word language plus a few cells near the
head is the next thing to try.
