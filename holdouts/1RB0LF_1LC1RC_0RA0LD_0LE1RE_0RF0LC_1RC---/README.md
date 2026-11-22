# 1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---

bbchallenge id 83189. One of the six-state holdouts whose halting from blank tape is open (group G11, family **two-ended counter, (10)^n left / 110 digits right**). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LF |
| B | 1LC | 1RC |
| C | 0RA | 0LD |
| D | 0LE | 1RE |
| E | 0RF | 0LC |
| F | 1RC | --- |

## Status

Open. Lean (kernel, 22 November 2026, `lean/Link.lean`): every token rule of the twin is a run of this machine's table and its rounds are the twin's rounds, so it never halts if from round 9 on every round's defect needs at most one visit (`nonhalt_of_need`, the twin's hypothesis in its `Fuel.lean`, word for word); with the twin's `Total.lean`, a tape with at most one defect cannot halt. (The first version of this, `nonhalt_of_clean`, assumed every defect dies from round 0, which is false: round 2's defect survives. Corrected the same evening.) Lean: the halting configurations and bounded runs (`lean/Blank.lean`); the halting context `1 C> 1 1` and 8 shift rules (`lean/Rules.lean`, kernel); the converse, that every halt passes through `1 C> 1 1` (`lean/HaltPred.lean`, kernel). C: no halt in 20,000,000,000 steps.

## What it does

Both ends of the tape grow logarithmically. The left end is a long run of 10 after a few 0s (24 copies at step 556,283,168, 25 at step 1,678,517,170). The right end is a run of 110 (15 copies at step 1.8·109). In between lies a word of short digits (10, 110, 1110) in no fixed order that changes at each pass, like the digits of a counter, and decides when the head next reaches the left end. It is the same kind of machine as 1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA. No exact rule for the middle has been found.

Halting: The halting transition is F reading a 1. F is entered from A reading a 1 (moving left) or E reading a 0 (moving right). A is entered only from C reading a 0, which writes a 0 to A's left, so the first way is impossible. E is entered from D reading a 0 (moving left, and then F reads the 0 D wrote) or a 1 (moving right), so the halt needs D> 1 0 1; D is entered only from C reading a 1 and moving left, which gives 1 C> 1 1. Lean proves the steps from each context to the halt (halt_ctx, halt_ctx_A, halt_ctx_E), and the converse: a configuration halts three steps later if and only if it is 1 C> 1 1 (halt_iff_3, lean/HaltPred.lean). In the first 109 steps C had 1 C> 1 0 about 2.9·107 times and 0 C> 1 1 about 8.8·107 times, but never 1 C> 1 1: two of the three cells match all the time, the third never.

C's surroundings in 10^9 steps (`./ctxcount M 1e9 C 3 -1`): `0 C> 1 0` 29,411,582, `0 C> 1 1` 88,235,359,
`1 C> 0 0` 147,058,544, `1 C> 0 1` 29,411,751, `1 C> 1 0` 29,412,045, `0 C> 0 0` 22 times, never `1 C> 1 1`. Inside
the tape the runs of 1s have length 1 to 3; runs of 0s of length 3, 6, 9, 12 are rare (25, 7, 1, 1 in 300 sampled
tapes) while 4, 5, 7, 8, 10, 11 are common, a hint of a residue mod 3 that a proof would track.

Automata tried: `../1RB0LA_1RC1RA_1RD1RE_1LC---_0RB1LF_1RA0LE/c/far.c` (finite automata reduction) finds no
certificate with a DFA of at most 7 states on either side.

## Update, 18 November 2026

The twin's README now has a fourth pass on the missing lemma
([section](../1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF/README.md#fourth-pass-18-november-2026-what-the-missing-lemma-really-asks)):
its token rules and conserved value are proved in Lean from the four visit functions, and the lemma turns out not to
be about biased digits but about how often the round's defect reaches the digit end of the tape (about one round in
three, independently from round to round). Still open for both machines.

## Update, 22 November 2026

On the twin ([fifth pass](../1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF/README.md#fifth-pass-22-november-2026-one-defect-in-lean-a-fast-engine-and-the-layers-of-the-counter)):

- Lean (kernel) now proves that a tape of the shared round system with at most one defect cannot halt
  (`lean/Total.lean` there). It applies to this machine through the correspondence `0 0 0 1 0 S_k`, which is
  still only observed (up to k = 18).
- A fast token engine (`c/toksim.cpp` there) followed the defect of every round for 500,000 rounds (more than
  2^944,371 steps of the twin): every defect died inside the tape, about halfway in.
- The top of the counter is understood exactly: the conserved value is 1/15 - (290/127) 2^-(k+2)/2 + O(2^-k)
  (288/127 and 2^-(k+1)/2 for odd k), so the far end of the tape is layers of period 4 and 28 and then frozen
  digits, about 1.6 k digits in all. Only the irregular bottom layer, about 0.27 k digits, is ever eaten by a defect.
  The missing lemma would follow if no defect ever crossed all of it in one round; not proved.
- Later the same day, on the twin: Lean proves that its four visit functions are runs of its transition table and that
  it never halts if every round's defect dies (`lean/Link.lean` there). For this machine the correspondence turned out
  not to depend on the run: started in E on `0 0 0 1 0 S`, this machine reaches `0 0 0 1 0 1 0 A(S)` on every one of
  2,000 random tapes S on which A(S) is defined, and halts on the rest. Its own visits close up on the token words
  with five entry forms (state and the two cells to its left), through which every token rule is a run of this
  machine (`py/twinforms.py` there). Not in Lean yet: this machine works the rule for `x L` another way, so it needs
  its own token rules or a bridge to the twin's.

## This machine in Lean (22 November 2026, later)

`lean/Link.lean` (written by `py/linkgen.py`) proves the correspondence with the twin on this machine's own generated
table `H83189.trans`, so nothing about it is observed any more:

- A token tape `w` is the half tape `E w` right of the head. Every kind of token visit is a run from an **entry
  form** (state, and the two cells left of the head, nearest first) that ends three cells further left, for any tape
  `L` further left, which it never reads:

  | visit | form | start | end |
  |---|---|---|---|
  | A (`FA`) | B after `1 0` | `E w` | E on `L0 · 0 0 · E w'` |
  | Ê (`FH1`) | C after `1 0` | `E w` | E on `L0 · 0 0 1 0 · E w'` |
  | Ê (`FH2`) | C after `1 1` | `E w` | D on `L0 · 0 0 0 0 · E w'` |
  | E0 (`FO1`) | B after `0 0` | `0 · E w` | E on `L0 · 0 0 · E w'` |
  | E0 (`FO2`) | C after `1 0` | `0 · E w` | E on `L0 · 0 0 · E w'` |

- `sound`: every token rule `TV` of the twin (`Tokens.lean` there) holds in every form of its kind. Each of the 25
  cases is a few stretches of 1 to 17 steps (by `rfl`) around calls of the rule's premises. `py/linkgen.py` finds
  them by symbolic simulation, taking a premise as a call wherever the head meets its input in one of its forms.
  The earlier worry that this machine works `x L` another way was an artefact of only calling visits on the tail:
  in the A form on `x L W` the head meets B after `1 0` on `x W` four cells to the right, then B after `1 0` on
  `A(x W)`, exactly the twin's `A(x L W) = L A(A(x W))`.
- `round_run`: in E on `0 0 0 1 0 · E S` (after two blank cells to the left) the machine reaches E two cells
  further left on `0 0 0 1 0 · E (x :: A(S))`; `start`: from blank tape it is in E on `0 0 0 1 0 · E []` after 4
  steps. So this machine's tape at every second visit of E to a new leftmost cell is `0 0 0 1 0 S_k`, now a theorem.
- `round9`: from blank tape this machine is in E on `0 0 0 1 0 · x a9` (blank to the left) at step 7,834, the start
  of round 9 (kernel evaluation of the list simulator; the twin gets there at step 5,848).
- `nonhalt_of_need`: with the twin's `Z36869.total` and `F36869.dies` (`Need.lean` there), if in every round from 9
  on the round tape `x W` has `nx W ≤ 1`, this machine never halts from blank tape. The hypothesis is the twin's
  `F36869.nonhalt_of_need` word for word (`nx`, `R9` from the twin's `Need.lean`). Axioms: `propext`, `Quot.sound`.
- **Correction.** The first version (PR 416) proved `nonhalt_of_clean`: never halts if every round's defect dies,
  counted from blank tape. That hypothesis is false: `S_2 = x L O I` and `A(x L O I) = L I x I`, so round 2's
  defect survives (`F36869.old_hyp_false` in the twin's `Fuel.lean`), and the theorem was vacuous. It is removed;
  `nonhalt_of_need` replaces it.

So the two machines now stand or fall on one statement, and the twin's 500,000-round engine run (every defect died)
is a run of this machine's rounds too. A resumed 2,000,000-round run of that engine (from its checkpoint at round
300,000) is under way in `/mnt/project-files/defect-pair-run`.

## The rule of the middle (14 November 2026)

The middle word is now decoded, on the twin 1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF: see
[its README](../1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF/README.md#the-whole-run-as-one-counter-system-14-november-2026).
At every second visit of E to a new leftmost cell this machine's tape is `0 0 0 1 0 S_k`, where S_k are the round words
of that machine's mirrored tape, S_{k+1} = 1 0 A(S_k) (checked up to k = 18 with `py/twinchk.py` there; observed, not
proved). In the words `L = 1010`, `O = 000`, `I = 100` the tape is a binary counter with doublers, and each round sends
one defect through it. A tape with one defect cannot halt (by hand); the halting context `1 C> 1 1` needs two defects
side by side, and in 4,500 rounds every defect disappeared long before the next one started. The residues mod 3 of the
runs of 0s noted above are the 3-cell digits. No halt in 100,000 rounds of the twin. Open: that every round's defect
disappears in time.

## Files

- `lean/HaltPred.lean` (every configuration that halts after exactly k more steps, k = 1, 2, 3, both directions) is written by
  the batch's generator: `python3 ../1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB/py/halt_pred.py 1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC--- 1 2 3 > lean/HaltPred.lean`.
- `py/linkgen.py` writes `lean/Link.lean` (the twin's token rules as runs of this machine, the round law, `round9`, `nonhalt_of_need`):
  `python3 py/linkgen.py > lean/Link.lean`. `lean/check.sh` compiles the twin's `Tokens.lean`, `Total.lean` and `Need.lean` first.
- `lean/rules.py` writes `lean/Rules.lean` (the halting context and the shift rules, proved by `bbtools.symtm`):
  `cd lean && python3 rules.py > Rules.lean`.
- The near-miss counts come from `c/ctxcount.c` and `c/forbid.c` in
  [`../1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c`](../1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c) (shared by the
  batch): `./ctxcount M 1e10 S 3`, `./forbid M 1e10 S:111`.

## Next steps

Prove that from round 9 on every round's defect needs at most one visit (`nx W ≤ 1`, the twin's missing lemma); everything else is in Lean.

## Pages

- [`pages/holdouts/1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---/explainer.html`](../../pages/holdouts/1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---/explainer.html)
- [`pages/holdouts/1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---/proof-status.html`](../../pages/holdouts/1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC--- 20000000000
gcc -O2 -o ctxcount holdouts/1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c/ctxcount.c && ./ctxcount 1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC--- 1e9 C 3 -1
```
