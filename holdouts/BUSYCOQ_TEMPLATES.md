# The holdouts against busycoq's proof templates

busycoq's `BB6` branch (ccz181078/busycoq, commit `33209bc`, 3 November 2026) holds about 300 hand-written proof
templates: shift-overflow counters (`SOC*`, `SOBC*`, `SOMDC*`), sync bouncer counters (`SBC*`), bell eats counter
(`BEC*`), Skelet 1-like counters (`Sk1*`), `CounterClass*`, `Loop4*` and others. Each is a Coq section that proves
"this machine never halts" from a short certificate, and each comes with the list of machines it was applied to.
Can any of them be instantiated for our 608 holdouts? This page reports the search (24 November 2026).

**Result.** No template proves any holdout. That was expected: the holdout list is what was left after these
templates were run. The search shows where each one stops:

- **No exact fit.** Templates with fixed digit words do not match. For example, no holdout has both of `SOCv1`'s
  counters: its left counter uses digits `01/11` and its right counter uses `1000/0000`.
- **Transplants.** 81 holdouts are at most two transitions away from a machine that a template proves. We made 139
  copies of those proofs with the holdout put in, and compiled each one. None compiles.
- **Shift-overflow siblings.** For 12 of them, the counter increments and the first overflow rules are all proved
  for the holdout. What fails is the rule for the second overflow of the right counter (`SOC_2_3_v2`: `ROv2_0`,
  `ROv2_1`), or the third and fourth (`SOC_2_5_v1`). This is where these machines differ from their proved
  neighbours. Their folders here already describe it as the anomaly or collision cascade.
- **Counter census.** Only 41 holdouts have a head that bounces between two binary counters, the shape every
  `SOC*` template starts from. 21 of these are in family F02 and 8 in F03. Families F05 and F06 (block-list and
  Skelet 1-like counters) use no binary carry rule at all, so `SOC`/`SBC`/`BEC` templates cannot apply to them.

So a new proof for these machines needs a new overflow argument, not a re-run of an existing template. The
closest targets are in the last table.

## 1. Which counters the runs use

`tools/busycoq_templates/carry.c` lists every *carry rule* of a machine. A carry rule has the form

    E D1^n <{{Q}} M   -->+   F D0^n <* M' {{Q'}}>     for n = 0..6,

with digit words `D1`, `D0` of 1 to 4 cells (`D0` not a rotation of `D1`, which would only be a shift), a far
marker `E`, and a near word `M` of up to 2 cells. Right-side rules come from the mirrored machine. This is the
shape of `LInc`/`RInc` in every `SOC`, `SBC` and `BEC` template. `carryuse.c` then runs each holdout from blank tape
(10^7 steps, or 3·10^6 for the last 179 machines) and counts how often each rule's start pattern occurs, and with
what largest n. A rule counts as *in use* when n reaches 6. `classify.py` sorts each machine by what its run uses:

| family (plan/families.md) | two counters, head bouncing between them | counters on both sides, not linked | one counter | none |
|---|---|---|---|---|
| F01 periodic blocks + bounded engine | 0 | 3 | 10 | 43 |
| F02 clock-and-word, two-counter shift-overflow | **21** | 9 | 20 | 1 |
| F03 binary counters with markers and resets | **8** | 5 | 13 | 4 |
| F04 Collatz-like bells | 0 | 0 | 22 | 26 |
| F05 nested block counter | 0 | 0 | 0 | 45 |
| F06 Skelet 1-like countdowns | 0 | 0 | 0 | 45 |
| F07 chaotic bells | 0 | 0 | 14 | 39 |
| F08 counter beside a chaotic edge | 2 | 0 | 9 | 39 |
| F09 bouncers over lists of counters | 0 | 0 | 6 | 16 |
| F10 block-splitting mess | 0 | 0 | 7 | 35 |
| F11 defect gases, CA zones | 4 | 1 | 27 | 34 |
| F12 cryptids, parked | 0 | 8 | 14 | 26 |
| not in a family (proved or under review) | 6 | 3 | 13 | 30 |
| **total** | **41** | **29** | **155** | **383** |

As a check, the PR proofs of shift-overflow machines (1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC--- of PR 59,
1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE--- of PR 48) come out in the two-counter class. The digit widths (left,
right) of the 41 are (4,3) ×11, (2,3) ×10, (2,4) ×6, (4,2) ×5, (4,4) ×4, (3,3) ×2, (3,4) ×2 and (3,2) ×1. busycoq
has a `SOC_a_b` variant for each of these widths. So the digit sizes are not what stops a fit: the overflow rules are.
The counters each machine uses, with their words, states and largest n, are in `holdouts/busycoq_templates.json`
(`counters`).

## 2. Transplanting the nearest proofs

`near.py` collects the 240,490 machine strings in the branch's `verify/*.v` (equivalence files left out). For each
holdout it finds the proved machines that differ from it in at most 2 of the 12 transitions, as written or mirrored.
States are not renamed, so this misses neighbours that only match up to a renaming.
[`DEEPMIND_NEIGHBOURS.md`](DEEPMIND_NEIGHBOURS.md) did renamings for DeepMind's tables. 343 holdouts have such a
neighbour. For most of them the neighbour comes from a generic decider (CTL, RepWL, Inductive...), whose parameters
were already searched on the holdouts. For 81 holdouts the neighbour comes from a template.

`transplant.py` copies the template file and puts the holdout in place of the neighbour (the mirrored holdout when
the match was mirrored). `trim.py` then drops the other machines' proofs. Each copy is compiled with Coq 8.20.1
against the branch's `verify/`. A file that compiled would be a proof, but none did:

| busycoq file | holdouts | tries | outcome | first lemma that fails |
|---|---|---|---|---|
| SOC_2_3_v2 | 9 | 12 | goals left open | `ROv2_0`, `ROv2_1` (probe below) |
| SOC_2_3_v3 | 7 | 9 | a rule fails | `ROv2`, `ROv2_0_0` |
| SOC_2_3_v4 | 2 | 3 | a rule fails | `ROv2_0`, `RInc` |
| SOC_2_3_v5 | 1 | 1 | a rule fails | `extra_rule` |
| SOC_2_4_v3 | 1 | 1 | goals left open | every rule (probe) |
| SOC_2_5_v1 | 5 | 9 | goals left open / a rule fails | `ROv3_*`, `ROv4_*`, `ROv'_*` (probe) |
| SOCv1 (6x2 list) | 5 | 8 | a rule fails | (tactic leaves the cert's rules open) |
| SOCSSv2 | 1 | 1 | a rule fails | `R1_Inc` |
| SOMDCv1 | 5 | 5 | a rule fails | `hRL_110` |
| SOMDCv3 | 3 | 3 | a rule fails | `RIncs_spec` |
| SOMDC_Class1 | 3 | 4 | a rule fails | `C24_tail_window` |
| PR_SOMDC_Class1 | 6 | 8 | a rule fails | `zP0`, `seg_ca_V` |
| PR_SOMDC23Halt (halting proofs) | 8 | 15 | stopped at the time limit | (the accelerated run does not reach a halt) |
| SOBCv4 | 2 | 4 | a rule fails | `LBigStep_spec`, `Lprefix_halt` |
| SOBCv7 | 3 | 3 | a rule fails | `d0a_Inc` |
| SBCv2 (6x2 list) | 4 | 6 | a rule fails | (cert's rules) |
| SBCv7 | 1 | 2 | a rule fails | `LIncs` |
| SBCv8 | 3 | 3 | a rule fails | `Incs_w` |
| SBCv1 (6x2 list) | 1 | 2 | stopped at the time limit | |
| BECv1 (6x2 list) | 4 | 6 | stopped at the time limit | |
| IndBECv1, IndSBCv1 | 4 | 5 | a rule fails | |
| Sk1like_TC_v1 | 6 | 6 | a rule fails | `RInc_spec` |
| Sk1like_TC_v2 | 10 | 10 | a rule fails | `RInc_spec` |
| Sk1Class2_v2 | 2 | 2 | a rule fails | `T3` |
| CounterClass2v1, CounterClass3v1 | 3 | 3 | a rule fails / time limit | `sideRLs_D_Bo0_1`, `P0_n` |
| Loop4v1 | 3 | 4 | a rule fails | `Inc1`, `LOv0` |
| BMO7, CSv1, PR_TranslatedCounter | 4 | 4 | a rule fails | `RInc`, `Inc1_0`, `nonhalt` |

"Stopped at the time limit" means the tactic ran past 30 minutes (6.7 minutes for the last few halting copies)
without finishing, so these tries are undecided rather than failed. Each try, with its neighbour, is in
`busycoq_templates.json` (`transplants`).

## 3. The closest: shift-overflow siblings

In `SOC_2_3_v2` and `SOC_2_5_v1` the template's `es` tactic leaves a rule open instead of failing. So `probe.py`
re-ran the 15 copies with one `first [ only 1: (es; fail) | cycle 1 ]` per rule, which shows rule by rule what is
proved for the holdout. The start configuration and its arithmetic condition (`init`, `Pinit`) were left open in
every copy. They depend on the neighbour's numbers, which were not searched, so they say nothing.

| holdout | template | proved for the holdout | open |
|---|---|---|---|
| 1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RA--- | SOC_2_3_v2 | LInc, RInc, LOv, ROv1_0, ROv1_1 | ROv2_0, ROv2_1 |
| 1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RC--- | SOC_2_3_v2 | same | ROv2_0, ROv2_1 |
| 1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RE--- | SOC_2_3_v2 | same | ROv2_0, ROv2_1 |
| 1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC--- | SOC_2_3_v2 | same | ROv2_0, ROv2_1 |
| 1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RC--- | SOC_2_3_v2 | same | ROv2_0, ROv2_1 |
| 1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0RB--- | SOC_2_3_v2 | same | ROv2_0, ROv2_1 |
| 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB--- | SOC_2_3_v2 | same | ROv2_0, ROv2_1 |
| 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1RC--- | SOC_2_3_v2 | same | ROv2_0, ROv2_1 |
| 1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0LB--- | SOC_2_3_v2 (mirrored) | same | ROv2_0, ROv2_1 |
| 1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC | SOC_2_5_v1 (mirrored) | LInc, RInc, LOv, ROv1_0, ROv1_1, ROv3_0, ROv3_1 | ROv4_0, ROv4_1, ROv'_0, ROv'_1 |
| 1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB | SOC_2_5_v1 (mirrored) | same | ROv4_0, ROv4_1, ROv'_0, ROv'_1 |
| 1RB0RF_1RC1LB_1LD1RE_1LB0LD_1RF0RC_1RA--- | SOC_2_5_v1 | LInc, RInc, LOv, ROv1_0, ROv1_1 | ROv3_*, ROv4_*, ROv'_* |

(Three more copies had every rule open: 1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC--- against `SOC_2_5_v1` (mirrored,
one transition away) and against `SOC_2_4_v3` (two away), and 1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC--- against
`SOC_2_5_v1` (two away).)

Six of the first nine share one table, the G12 word-and-counter table `1RB?RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_?---`:
they differ only in A's 1-transition and in F's 0-transition. Their folders here already prove the regular macro steps in Lean and point to the
collision cascade at the second overflow as the open part. The other three are 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB--- and
1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1RC---, and 1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0LB---. The probe
confirms it from the other side: busycoq's own counter and first-overflow rules hold verbatim for them, and the
template stops exactly at `ROv2`. An `ROv2` that covers the cascade, with an invariant strong enough to keep the
word from running out, would be the new piece. The two `SOC_2_5_v1` siblings are the next nearest: they hold up to
the third overflow.

## Reproducing

Needs busycoq's `BB6` branch and Coq 8.20.1. The project's Nix export of 8.20.1 works; Ubuntu's 8.18 does not
compile the branch. Build the branch's core files in `verify/` first. Then, from `tools/busycoq_templates/`:

```
gcc -O2 -o carry carry.c && gcc -O2 -o carryuse carryuse.c
awk '{print $2}' BB6_holdouts_608.txt | ./carry > carry_all.txt          # about 2 s
./carryuse 10000000 < carry_all.txt > relev_all.txt                       # about 1 h on 4 cores, split by machine
FAMILIES=families.json python3 classify.py                                # counters.json, byfamily.json
BUSYCOQ_VERIFY=../busycoq/verify python3 near.py                          # near.json
python3 transplant.py ../busycoq/verify                                   # jobs.json and TXnnn.v copies
# compile each TXnnn.v in verify/ with coqc -Q . BusyCoq -Q ./BigInt BigInt; trim.py drops other machines' proofs
```

Here `families.json` is the plan's family list (`machines` per family), and the right-side words that `carry.c` prints
are mirrored. In Coq list order, every printed word is reversed, on both sides.
