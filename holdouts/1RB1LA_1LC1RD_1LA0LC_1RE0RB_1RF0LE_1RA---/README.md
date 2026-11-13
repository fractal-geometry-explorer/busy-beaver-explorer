# 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0LE_1RA---

Nobody knows whether this six-state, two-symbol Turing machine halts when started on a blank tape: it is one of the holdouts left open by the bbchallenge project. It belongs to a family of four holdouts that share their first four states, and works as two binary counters, one counting down in the blocks left of the head and one counting up in the gaps right of it. This page lists what is established, sorted by what each result rests on.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LA |
| B | 1LC | 1RD |
| C | 1LA | 0LC |
| D | 1RE | 0RB |
| E | 1RF | 0LE |
| F | 1RA | --- |

**Verdict.** **The question is open.** Lean now proves the counter itself: read the tape as two binary numbers, E in the odd blocks left of the head and N in the gaps right of it, and every countdown of E, for every size of E and N, runs as the counter says (`run3`, `run5`). Lean also proves that the blank-tape run enters this counter after 256 steps and runs its first countdown. The pass rules (including the halting one) are proved too. What is not proved is what happens between countdowns. When E runs out the tape is reorganised; the reorganisation leaves *defects* on the right (gaps of an irregular size, blocks of two 1s), and the machine halts only if such defects meet in one particular way. No invariant excluding this is known. An accelerated simulation reaches 9.70·10^171 steps with no halt.

## What it does

One of four holdouts (1a `..._1RB0RF_0RB---`, 1b `..._1RB0RF_1RC---`, 1c `..._1RF0LE_1RA---`, 1d `..._1RF1RC_1RA---`)
that share states A–D, `1RB1LA_1LC1RD_1LA0LC_1RE0RB`. The family's scripts are in `holdouts/1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB---/`.

At the start of a *pass* (head in state A on a 0, a block `1^m` to its right) the tape is

    0^inf 1^(2s) 0 1^(2v_1+1) 0 1^(2v_2+1) ... A>0 1^m 0^(5q_1+4) 1 0^(5q_2+4) 1 ... 0^inf

A pass eats the top block two cells at a time (A, B, C carry 1s to the left part; D runs right into the first gap):
m even: two 1s go left, the first gap shrinks by one; m odd: D crosses all gaps of the smallest size and cuts the
first larger one; m = 2, 3: the block merges with the left part (`lean/Rules.lean`, all proved for every parameter).

Read the odd blocks on the left as the binary digits of a number E (a block `1^(2v+1)` is a 1 bit followed by v zero
bits) and the gaps on the right as the digits of F. One *cycle* of passes maps (E, F) to (E − 1, F + 1) in
a + 4ν(E) + 6ν(F+1) steps (ν = 2-adic valuation; a = 54 in the commonest shape of 1a): two binary counters. When E runs
out, a *phase transition* starts a new countdown (round 2: the new E comes from the floor block, see below) (1a: phases end at 4,071,811, 8,593,882,720, ~3·10^23, ~10^42, ...).
Transitions are irregular: they can leave a long gap (a reservoir that later overflows of F eat 5 cells at a time) and
short sub-phases in other shapes.

The machine halts only when F reads a 1, and from a pass start that happens exactly when an odd pass, after the small
gaps, meets a gap one cell too short (`pass_odd_halt`). During a countdown all gaps are at least 4 long, so only a
phase transition can create the fatal gap. Whether one ever does is the open question.

### Round 2: the counter exactly, and the transitions

Read the tape at the start of a pass as two binary numbers. Left of the head, going outward, every pair of cells is one bit of *E*, lowest bit first: `1 1` is a 0 and `1 0` is a 1, down to an even block, the *floor*. Right of the head, after the top block, every group of 5 cells is one bit of *N*: `0^5` is a 0 and `0^4 1` is a 1. (So an odd block `1^(2v+1)` is v zero bits and a one bit, and a gap is a run of zero bits closed by a one bit.)

With top block `1^3` (mode 3) one pair of passes subtracts 1 from E and adds 1 to N; with `1^5` (mode 5) two pairs subtract 1 from E and add 2 to N. A pair costs a constant plus 4 steps per trailing zero of E plus 10 per trailing one of N, exactly the work of borrowing and carrying.

When E reaches 0 the floor `1^(2s)` is popped into the top block; the next pass pushes s single 1s, which is E ≈ 2^s − 1, all ones, and the mode switches between 3 and 5. N is left on the right, but the pass that cut it leaves a gap of the wrong size, a *defect*, in front of it.

Defects are worked off in a cascade of short sub-phases: a gap one cell too long collapses into a block `1^2`; a block `1^2` followed by a gap makes the next gap one too short; a gap one too short followed by a single 1 is cut and hands its defect to the next gap. Sometimes N is swallowed into the left part entirely and restarts at 0. Then a clean countdown runs again. Since the floor gains 2 cells each time E passes a power of two, the floor is about twice the bit length of the largest E so far, and phases grow fast.

The machine halts only when F reads a 1. From a pass start that happens exactly when an odd pass, after the gaps of the smallest size, meets a gap of length one followed by a block of two or more 1s (`pass_odd_halt`, proved). In the language above that needs *two* defects at once: a gap cut down to length one, directly in front of the `1^2` left by another defect. In every transition seen so far a single defect was worked off without harm.

During a countdown there are no defects at all, so a halt can only come inside a transition cascade. The defect monitor of `c/ps.c` was not run on this machine in round 2 (it was run on 1a and 1b, where there was never more than one defect at a time).

## What is established

**Proved in Lean, kernel only:**

- **The halting configurations.** The machine stops exactly when it reads the symbol of a halting transition (F1); the generated statement covers every configuration. (`step_none_iff`, `lean/Blank.lean`)
- **No halt in the first 10,000 steps.** The list simulator of the shared library, proved to agree with the machine's semantics, runs 10,000 steps from blank tape without a halt, evaluated by Lean's kernel. (`blank_runs_kernel`, `lean/Blank.lean`)
- **The pass rules.** Six rules on symbolic tapes, for all values of their parameters and any surrounding tape: a pass on an even top block (`L 1 A>0 1^(2k+4) 0^(g+4) 1 R`), on a block of 2, on an odd block crossing j small gaps, on a block of 3, a gap of length one closing, and `pass_odd_halt`: an odd pass whose D-run meets a gap one cell too short reaches F reading a 1, the only halting transition. Proofs by `rfl` steps and crossing lemmas, written by `tools/py/bbtools/symtm.py`. (`lean/Rules.lean`, `holdouts/1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB---/py/gen_rules.py`)
- **The counter, proved for every size.** Write E in p bits on the left (from the head outward, a 0 bit is `1 1` and a 1 bit is `1 0`, above a floor that starts with a 1) and N in n bits on the right (a 0 bit is `0^5`, a 1 bit is `0^4 1`, followed by any tape X). In mode 3 (top block `1^3`) the machine takes (E, N) to (E − k, N + k) for every k ≤ E with N + k < 2^n, in at least 26·k steps (`run3`); in mode 5 (top block `1^5`) it takes (E, N) to (E − k, N + 2k) in at least 56·k steps (`run5`). Proofs: three pass-pair rules written by `tools/py/bbtools/symtm.py`, the binary decrement and increment on bit lists, and induction on k. (`lean/Counter.lean`, generated by `holdouts/1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB---/py/gen_counter.py`)
- **The blank-tape run enters the counter.** After 256 steps from blank tape the machine is in mode 5 with E = 35 (6 bits) and N = 1 (`init_counter`), and it then counts E down to 0, reaching N = 71 after at least 1960 further steps (`first_countdown`). (`lean/Init.lean`, generated by `holdouts/1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB---/py/gen_init.py`)

**Proved in Lean with `native_decide`:**

- **No halt in the first 10^7 steps.** The same run, evaluated by compiled code. (`blank_runs_native`, `lean/Blank.lean`)

**Trusted computation (C/Python, not Lean):**

- **No halt in the first 10^9 steps.** The C simulator `tools/c/triage.c` runs 10^9 steps without a halt; at the end 181 cells have been visited and 64 of them hold a 1. (`holdouts/triage.json`)
- **No halt in the first 2·10^10 steps.** Direct simulation with `tools/c/tmrun.c`. (`tmrun 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0LE_1RA--- 20000000000`)

**Heuristic:**

- **Growth shape: exp/fixed.** Left of the start, the visited part of the tape stopped growing in the second half of the run (bounded so far, or growing so slowly that no record fell in the last half). Right of the start it grows like the logarithm of the step count: each new cell costs a roughly constant factor more time, the signature of a *counter* or of a Collatz-like map whose values are written on the tape (fitted exponent 0.047). (`tools/py/bbtools/triage.py`)
- **No halt before 9.70·10^171 steps.** The family's accelerated simulator `py/accel.py` (with `c/acc.c`, in the folder of 1a) runs the machine directly until a shape repeats 12 times with E → E − 1 (or E − 2^k) and F → F + 1, fits the step formula a + b·ν(E) + g·ν(F+1) exactly, checks the first min(N, 2^15) cycles of the jump against direct simulation token for token, and then jumps N cycles. It made 73 jumps (E up to 571 bits) with no failed check and no halt. That the formula holds for the whole jump is a pattern, not a proof. (`GB=4 GP=5 XEFF=0 python3 holdouts/1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB---/py/accel.py 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0LE_1RA--- 300`)
- **The phase transition.** When E reaches 0 the floor block `1^(2s)` under it is popped into the top block, the next pass pushes s single 1s, and a new countdown starts with E = 2^s − 1 (s one bits; floor `1^2`) in the other mode (3 and 5 alternate); N stays on the right, but the cut leaves a gap of irregular size in front of it. Irregular gaps then act in a cascade of short sub-phases: a gap one too long (for 1a/1b; the analogous residue mod 5 for 1c/1d) collapses into a block `1^2`, a gap one too short followed by a single 1 is cut down and passes its defect on to the next gap; sometimes the whole of N is pulled to the left and N restarts at 0. The floor grows by 2 whenever E passes a power of two, so it is about twice the bit length of the largest E so far. Seen at every transition of the runs above; not proved, and no closed formula for the new (E, N) as a function of the old one is known. (`holdouts/1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB---/py/jump2.py` (log of the tapes at each counter start))

**Open:**

- **Does it halt from blank tape?.** Not known. By `pass_odd_halt` the machine halts exactly when an odd pass, after the gaps of the smallest size, meets a gap of length one followed by a block of two or more 1s. In the counter language this needs two defects to meet: an irregular gap cut down to length one directly in front of a `1^2` block left by another defect. During a countdown there are no defects (proved: the countdown is `run3`/`run5`), so it can only happen inside a transition cascade. In the runs above there was never more than one defect at a time; no invariant proving that is known, and the transitions have not been reduced to a number-theoretic map.

## Reproduce

From the repository root:

```
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0LE_1RA---/lean/check.sh
cd holdouts/1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB--- && python3 py/gen_rules.py 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0LE_1RA--- H150065 | diff - ../1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0LE_1RA---/lean/Rules.lean
gcc -O2 -o holdouts/1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB---/c/acc holdouts/1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB---/c/acc.c && GB=4 GP=5 XEFF=0 python3 holdouts/1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB---/py/accel.py 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0LE_1RA--- 200
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0LE_1RA--- 20000000000
```

## For later

More than a day of work remains. The counter is proved (`lean/Counter.lean`), so what is left is the transitions. Next steps: (1) prove the transition events as symtm rules (floor pop, the cut that leaves a defect, the gap-collapse and defect-passing events; the event patterns need an explicit continuation after the gap or symtm stops with TouchContext); (2) define a defect-aware configuration (counter plus at most one defect, with its position and type) and try to show it is closed under a countdown followed by a cascade; if two-defect configurations are unreachable this gives non-halting with Lean, combined with `init_counter`; (3) failing that, log (E, N, defect) at each counter start from `py/jump2.py` and look for a closed form of the transition map, which would turn the question into a number-theoretic one.
