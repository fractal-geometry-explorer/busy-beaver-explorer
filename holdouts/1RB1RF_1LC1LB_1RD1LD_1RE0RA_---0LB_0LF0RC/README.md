# 1RB1RF_1LC1LB_1RD1LD_1RE0RA_---0LB_0LF0RC

bbchallenge id 279. One of the six-state holdouts whose halting from blank tape is open (group G07).
Family: **nested counters driven by a Collatz-like block map**. Decision: **open**.

In one sentence: the tape is two growing blocks followed by a short list of counters; the first counter loses 1
every few epochs while the blocks are rebuilt by a rule that divides by 4 with cases on remainders; when the first
counter runs out the machine either halts (proved in Lean for the configurations in question) or builds new,
much larger counters, and which of the two happens depends on remainders that nobody can predict. The first
run-out, at step 2.995·10^23, did not halt; the second is due after about 10^(10^11) steps.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RF |
| B | 1LC | 1LB |
| C | 1RD | 1LD |
| D | 1RE | 0RA |
| E | --- | 0LB |
| F | 0LF | 0RC |

## The tape as a list of run lengths

Look at the tape each time the head reaches a new leftmost cell in state D, and write it as the lengths of its runs
of 1s, left to right, with single 0s between runs (an empty run, written `0`, is a double 0). From step 1,096 on the
tape at these visits reads

    3  2^n  3^p   FRONT   3^X  s 3^k1  s 3^k2 ... 1

- `2^n 3^p`: the two growing blocks (the cells `(011)^n (1011)^p` of the earlier notation `Y n p R`);
- `FRONT`: what the blocks are eating: a marker (a run of 1 or 5), a long run of 1s, or pairs `(3 1)^K`;
- then runs of 3 cut into **counters** `3^X`, `3^k1`, `3^k2` by **separators** `s`, each one of the runs 0, 2, 4;
- the final run `1` at the right end of the tape.

For example at step 10,629 the tape is `3 2^15 3^14 0 3^22 0 3^4 1`.

### Between two visits: three local rules

Each visit adds one run of 2 at the left (n+1). What happens at the front depends only on the first runs after `3^p`
(N is any run length):

    N        ->  3, N-4      for N >= 4      a long run loses 4 cells, the block of 3s gains a run (5 -> 3 1, 4 -> 3 0)
    1, N     ->  N+2                         a marker 1 takes the next run (1 3 -> 5: the marker moves one run right)
    1, 1, N  ->  3, N

So a marker walks through a counter `3^X` at one run per two visits (`5 3 -> 3 1 3 -> 3 5`), a long run `N` is eaten 4
cells per visit, and pairs `(3 1)^K` are eaten two pairs per three visits; n and p grow by one each time. These are
`grow` (the first rule for N >= 6), `eat` (two visits of the marker) and `marker1` in `lean/Rules.lean` and
`lean/HaltRule.lean`, proved for all n, p and any tape behind; all three were also checked against the plain machine
on every instance with small sizes (`py/runlist.py rule`).

### Events: the block of 2s is rebuilt

When the front reaches a separator, the head makes one long excursion. In most cases the whole block `2^n` is
rewritten into pairs, `2^n -> 4 5 (3 1)^((n+1)/2)` (n odd) or `4 3^2 (1 3)^(n/2+1)` (n even), which the blocks then eat
again: that is an *epoch*. What happens at the separators (large counts, `a b c` the counters, the rebuilt block
left out):

| front | becomes | |
|---|---|---|
| `3^p 1 0 3^a s ...` | `3^p 0 3^(a-1) s ...` | a marker reaches a counter: **the counter loses 1** |
| `3^p 0 3^a 4 ...` | `3^(p-1) 2 3^a 0 ...` | the two separators change |
| `3^p 2 3^a 0 3^b 1` | `3^(p-1) 0 3^a 4 3^b 1` | the same, last two separators |
| `3^p 2 3^a 0 3^b 4 3^c 1` | `(4p+1) 3^(a-1) 2 3^b 0 3^c 1` | the block of 3s becomes one long run of 4p+1 cells |
| `2^n 3^p 0 3^a 0 3^b 1` | `2^(n-2) 3^2 4 3^(p-1) 4 3^(a-1) 4 3^b 1` | no rebuild: **the block of 3s becomes a new counter** |
| `3^p 0 4 3^a 1` | `2^(n-2) 3^2 4 3^(p+a+1) 1` | an empty counter is absorbed |
| `3^p 1 0 4 3^a 1` | `3^(p-1) 1 3^a 1` | a marker passes an empty counter: **this configuration halts** |

(`py/runlist.py rule CONFIG` prints the rule of any shape; the table is its output for these shapes.) To leading
order an epoch that starts with K pairs and a counter X in front ends with n = 3K/2 + 2X, p = 3K/2 + X if a marker
survives the pairs (then the next counter loses 1) and with n = 3K/2, p = 3K/2 + X if not, and the next epoch has
K' = n/2 pairs: **K' = 3K/4 + X or 3K/4**, with the case and the rounding decided by remainders of n and K. This is a
Collatz-like map on numbers that grow by a factor of about 4 to 8 in steps per epoch.

## The first counter and what happens when it runs out

From step 6,183 to step 3·10^23 the tail is `3^X s 3^k1 s 3^4 1`: the counter k1 starts at 22 and loses 1 every few
epochs (19 by 10^5 steps, 17 by 10^8, 6 by 10^18, 1 at 2.7·10^22); the last counter stays 4. Events 55 to 59
(`py/runlist.py events 27`) are the run-out:

    2.67e22   3^p 1 0 3^2 4 3^4 1   ->   3^p 0 3 4 3^4 1           k1: 2 -> 1
    4.46e22   3^p 0 3 4 3^4 1       ->   3^(p-1) 2 3 0 3^4 1
    2.995e23  3^p 0 3 0 3^4 1       ->   3^2 4 3^(p-1) 4^2 3^4 1   k1: 1 -> 0, the block p = 103352228706 becomes a counter
    2.995e23  3^p 0 3^103352228705 0 4 3^4 1  ->  3^2 4 3^(p-1) 4 3^103352228710 1

so the old last counter 4 is absorbed, the new last counter is 103,352,228,710 and the new first counter is
131,245,843,096. It has lost 143 by 10^159 steps and 199 by 10^210 (about one per factor of ten in steps): it runs
out after about **10^(10^11) steps**, far beyond any exact simulation (the numbers themselves would have 10^11 digits, and the
block map has no known shortcut).

**What a run-out can do.** `lean/Halt.lean` proves, for every n, p, k:

    halts_marker5:  0^inf D> 0111011 (011)^n (1011)^p (1110)^(k+1) 1 0^inf      (runs  3 2^n 3^p 5 3^k 1)      halts
    halts_marker1:  0^inf D> 0111011 (011)^n (1011)^p 1010 (1110)^k 1 0^inf     (runs  3 2^n 3^(p+1) 1 3^k 1)  halts

a marker with nothing but the last counter behind it walks to the end of the tape, and the machine stops there
(E reads a 0 past the last run). By the last row of the table this is what happens when a marker reaches an empty
first counter. Experiment (`py/runlist.py exhaust`, run-list simulator, see below): the configuration of step
1.1·10^27 with its first counter replaced by J: J = 0, 3, 6 halt (after the marker has eaten the last counter,
2·10^11 visits later); J = 1, 2, 4, 5 and 7 to 29 do not: they end with two or three new counters of 15 to 28 digits and go
on. Varying the front as well (J = 2, 5, 9 with 20 different numbers of pairs each): 7 of the 60 runs halt. So a halt is not excluded by the structure; it is one of the outcomes of a run-out, chosen by remainders.

## Where it can halt

The machine halts only on E reading 0, entered from D reading 0: D must read a 0 with another 0 right of it. The CTL
search of `bbtools.ctl` (K = 6) allows this only at the right end of the tape, and the only way there found so far
is the marker walk above.

## Evidence and tools

- `c/dv.c`: the plain machine, printing the run list at every visit. `c/syn.c`: the plain machine started from a
  given run list (the oracle of the simulator below).
- `py/ctxmacro.py`, `py/accel.py`: the exact macro simulator (blocks of 12 cells, one-block context) with proved
  linear cycle jumps (`bbtools.cycles`). `accel.py check` compares it with the plain macro run. It reaches 10^210
  steps without a halt (30 minutes); `py/dforms.py` writes its visits as run lists.
- `py/rls.py`, `py/runlist.py`: a simulator on run lists whose rules are *learned* from the plain machine (small
  instances of each shape, affine fit, checked on further and far instances) with closed-form jumps over
  repeating cycles. It is a computation to be validated, not a proof; it agrees with the plain machine on every
  visit to 3·10^9 steps (`runlist.py check`) and with the accelerated macro run, tape and step count, at all 3,172
  of its visits written by `dforms.py` up to 3.4·10^158 steps (`runlist.py accel`), and it is about ten times faster.

## Status

Open.

- **Kernel:** `step_none_iff`, `blank_runs_kernel` (`lean/Blank.lean`); the local rules `grow`, `eat` and their
  iterations (`lean/Rules.lean`, `lean/Phase.lean`); `tail`, `tail2`, `marker1` (`lean/HaltRule.lean`); the halting
  criterion `halts_marker5`, `halts_marker1` (`lean/Halt.lean`). **native_decide:** `blank_runs_native` (10^7 steps).
- **Trusted computation:** no halt in 10^210 steps (`py/accel.py run 210`, exact macro run with proved jumps); the
  run-out of the first counter at step 2.995·10^23 and the counters after it.
- **Computed with learned rules (validated as above):** the rule table, the event list, the run-out experiments.
- **Heuristic:** the next run-out at about 10^(10^11) steps; that each run-out halts with a probability
  bounded away from 0 (so that the machine would halt eventually, but not within any reachable time).
- **Open:** whether it halts. A proof of non-halting would have to show that no run-out ever lets a marker
  through, against the experiments above; a proof of halting needs the remainders at a run-out that far away.

### Next steps

- Prove the rule table (each row is a single excursion with all counts symbolic; `bbtools.symtm` proves the local
  rules, the rebuild of `2^n` needs an induction on n) to make the run-list system a Lean object.
- Decide whether the choice at a run-out can be read off small remainders of the counters (it depends on which
  of the events `1 0`, `0`, `2` arrive while the first counter is 2, 1, 0): then the next run-out might be decidable
  with modular arithmetic alone, without the 10^11-digit numbers.

## Accelerated run (13 November 2026)

Observed, not proved: the accelerated simulator `rsim.py` ran 6.44x10^2890 steps from blank tape without reaching a halting transition. Its tape, state and head position were equal to those of a plain C simulator at 6 checkpoints, the last at 2.56x10^10 steps. Of these steps, the part after the last checkpoint rests on the simulator alone, including 10,834 trip-level jumps: a jump applies many identical round trips at once after seeing the same tape shape recur with constant count changes, which is validated against direct simulation but not proved.

```sh
python3 holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/py/rsim_screen.py 1RB1RF_1LC1LB_1RD1LD_1RE0RA_---0LB_0LF0RC 400
```

## Pages

- [`pages/holdouts/1RB1RF_1LC1LB_1RD1LD_1RE0RA_---0LB_0LF0RC/explainer.html`](../../pages/holdouts/1RB1RF_1LC1LB_1RD1LD_1RE0RA_---0LB_0LF0RC/explainer.html)
- [`pages/holdouts/1RB1RF_1LC1LB_1RD1LD_1RE0RA_---0LB_0LF0RC/proof-status.html`](../../pages/holdouts/1RB1RF_1LC1LB_1RD1LD_1RE0RA_---0LB_0LF0RC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RF_1LC1LB_1RD1LD_1RE0RA_---0LB_0LF0RC/lean/check.sh
cd holdouts/1RB1RF_1LC1LB_1RD1LD_1RE0RA_---0LB_0LF0RC/py
python3 rules.py | diff - ../lean/Rules.lean && python3 halt_rule.py | diff - ../lean/HaltRule.lean
python3 runlist.py check 3e9           # run lists against the plain machine, every visit (30 s)
python3 accel.py check 1e12            # accelerated macro run against the plain macro run
python3 dforms.py 160 /tmp/df.txt && python3 runlist.py accel /tmp/df.txt     # 15 min + 2 min
python3 runlist.py events 27           # the 69 events to 10^27 steps, the run-out at events 55-59
python3 runlist.py exhaust 0 30        # what a run-out does, for 30 values of the first counter (8 min)
python3 runlist.py halt "0 3 2^9 3^21 1 3^9 1"      # a marker in front of the last counter: halts after 9126 steps
```
