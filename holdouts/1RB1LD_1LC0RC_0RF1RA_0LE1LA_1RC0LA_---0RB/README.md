# 1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB

bbchallenge id 170561, group G10 (one side grows like √t, the other like a smaller power). Family: **Collatz-like: blocks split 1:3 by quarters**. Halting from blank tape: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LD |
| B | 1LC | 0RC |
| C | 0RF | 1RA |
| D | 0LE | 1LA |
| E | 1RC | 0LA |
| F | --- | 0RB |

## The event map (proved, exact)

At an **anchor** `Y 1^m D> 0 1^c Z` (state D on a single 0, m ones on its left, c ones on its right) the machine reaches the next anchor by one of these rules, each proved in `lean/Events.lean` for every block length and every surrounding tape:

| event | when | effect |
|---|---|---|
| split | m even, ≥ 4, two or more 0s left of the block | `Y 0 0 1^m D> 0 1^c` → `Y 1^(m/4) 0 0 1^(m%4) D> 0 1^(c+3(m/4))` |
| odd | m odd, ≥ 3, Y not empty | `Y 0 1^m D> 0 1^c` → `Y 1^(m-2) D> 0 1^(c+3)` |
| fold | m odd, ≥ 3, at the left end of the tape | `1^m D> 0 1^c` → `1 D> 0 1^(c+3(m-1)/2)` |
| shift | m even, too few 0s on its left for a split | `Y 0 1^m D> 0 1^c` → `Y D> 0 1^(m-1) 0 0 1^c` |
| two | m = 2 | `Y 0 0 1 1 D> 0 1^c` → `Y 1 0 0 0 0 1^(c-2)` + carrier |
| zero, one, oneE, oneO | m = 0 or 1 | the remainder is handed across the gap; in most cases the head runs right behind a carrier `0 1`, which passes blocks that follow a single 0 and becomes `1 1 1` at the first `0 0` or at the end of the tape |

Theorems: `event_sem` (an event is a run of the machine), `F_sem` and `halts_iff` (the machine halts from blank tape iff the orbit of the map F, an event where one applies and one machine step otherwise, reaches a halting configuration), `events_forever` (if the events alone can be iterated for ever from the first anchor, the machine never halts), and in `lean/Far.lean` `no_halt_kernel` (no halt in the first 10^130 steps, 30,000 events evaluated by the kernel) and `no_halt_native` (no halt in the first 10^13179 steps, 2,999,957 events, compiled).

Shape of the run: after a fold the tape is `1 D> 0 1^N`; splits cut the block into pieces (a quarter left, three quarters right, again and again), odd rounds glue the pieces back together, and a fold at the left end turns every 2 ones into 3. Which of these happens depends on the block lengths mod 4 and their parities: Collatz-like, open. A halt needs an anchor that no rule covers (a right block that is too short, or the carrier meeting a lone 1); none occurs in the first 2,999,957 events.

The explainer page replays this map in the browser (rule viewer on the real machine, event-by-event stepper). Its sources are in `holdouts/1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB/explainer/` (`core.js`, `spec.js`, `widget.js`, `build.py` for both machines of the pair); `node holdouts/1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB/explainer/test.js 4e8` checks the JavaScript against the plain machine (every viewer example; the first 457 events of this machine's run).

The sections below are the earlier, partial description (a different phase of the same rounds); the event map above supersedes it.

## What it does

After the start the tape is always a handful of long blocks of 1s, separated by gaps of one, two or four 0s, e.g. `1^1840 0 1^1387 0 1^1041 0^2 1^780 0^4 1^2338 0 1` at step 298,989,466. Everything the machine does is arithmetic on these block lengths.

**Splitting by quarters.** In state E, at a gap of two 0s before a block of M ones: `1^a E> 0 0 1^M 0 0 1^b`. If M is odd, a bouncer runs through the block and back and the tape becomes `1^(a+1) E> 0 0 1^(M−4) 0 0 1^(b+3)`: four ones leave the block, one goes left and three go right. Lean proves this round for every odd M ≥ 11 and every tape around (`quarter1`, `quarter3`, `quarter5` in `lean/Rules.lean`, 12n + 25 steps for M = 6n + 11 …); `py/split.py` checks it for odd M from 5. Repeated, it turns M = 4q + r into q ones added on the left and 3q on the right. In the run: 7359 = 4·1839 + 3 becomes `1^1840 … 1^5544` (1840 = 1 + 1839, 5544 = 27 + 3·1839), then 5544 → 1387 + 4158, 4158 → 1041 + 3118, …

**Folding.** An even block cannot be split this way; instead the head zig-zags between it and its left neighbour, moving two ones out of the neighbour and three into the block each time: `A>0 1^90 0^2 1^7227` → `A>0 1^88 0^2 1^7230` → … → `0^2 1^7362`. So a neighbour of 2n ones is merged as 3n. Lean proves this for every n, every M ≥ 1 and every tape to the right (`fold`, `fold_full` in `lean/Fold.lean`): `A> 0 1^(2n) 0 0 1^M` reaches `A> 0 0 0 1^(M+3n)`, then `A> 0 1 1 0 1^(M+3n)`.

These two moves (×1/4 and ×3/4 for odd blocks, ×3/2 for the fold) and the small cases at the end of a split (remainders 0–3, gaps of four 0s) make a Collatz-like map on the list of block lengths. The largest block grows like the square root of the step count (22,527 at step 1.87·10^9).

## Halting

F reading 0 halts. On small examples the split halts when it ends with M = 0, 2 or 4 in the shape above (the head meets three 0s in state E: E0 → C0 → F0), that is, when a split starts on an even block.

Parity pattern (heuristic, from an event log of the first 3·10^8 steps): every one of the 23,443 split rounds starts on an odd block (14,388 with M ≡ 3, 9,055 with M ≡ 1 mod 4), every block folded at the left end is even (7,115 zig-zags), and every round that starts at the left end as `A>1^K` has K odd. A split ends with M = 1 or 3 (`end1`, `end3`, proved) and hands over to the next block through a carrier `0 1` that runs right across it (`carry`, proved); what happens next depends on the neighbouring blocks (the right end of the tape, a gap of one or two 0s) and is not written down as rules yet. If the parity pattern is preserved by those endings, the machine never halts. Open.

Closed tape language with 5-cell windows (`python3 -m bbtools.ctl M 5`, trusted Python check): a halt (F reading 0) needs `00000` or `00110` to the left and `01001`, `0111x`, `01110` or `01111` on the right (8 abstract configurations).

## What is proved

- `lean/Blank.lean` (generated): the halting configurations (`step_none_iff`); no halt in 10,000 steps (kernel) and 10^7 steps (`native_decide`).
- `lean/Rules.lean`: `quarter1`, `quarter3`, `quarter5` (kernel), see above.
- `lean/FoldRules.lean` (written by `py/fold_rules.py` with `bbtools.symtm`): `fold_step`, `fold_last`, `fold_open`, and the first steps of the split endings `end1` (`1 E> 0 0 1 0 0 1 1` → `1 1 0 0 0 0 0 1 A>`), `end3` (`1 E> 0 0 1 1 1 0 0` → `1 1 0 1 0 0 0 1 A>`), `carry` (`0 1 A> 1^m 0` → `1^m 0 1 A> 0`, 5m steps), `lsweep` (kernel).
- `lean/Fold.lean`: `fold` and `fold_full`, the fold for every size, by induction (kernel).

Everything else here is observation of the run (heuristic) or a trusted computation, as marked in `status.json`. Nothing proved here decides halting.

## Evidence and how to reproduce

```sh
./tmrun 1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB 1000000000 records 100000      # tapes at each new cell
./tokrun 1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB 1000000000 a=10,b=110 L 100000 # the tape as words at the left end (R for the right)
python3 -m bbtools.ctl 1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB 5                # (from tools/py) the closed language and its halts
```

`python3 holdouts/1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB/py/split.py` checks the rule above on small configurations.

## For later

Write the rest of the split endings as symbolic rules: after `end1` / `end3` the carrier crosses the next block, and then, depending on whether that block is followed by the right end of the tape or by a gap of one or two 0s, a left sweep starts a new split or a fold. With those cases proved, check whether "every split starts on an odd block" is preserved; if it is, that is a nonhalting proof.

## First look

Growth class **power/sqrt** (left: sqrt, exponent 0.398; right: power,
exponent 0.121). After 1,000,000,000 steps: 12,322 cells visited (8,350 left of the
start, 169 right), 12,317 ones.

- left, step 763,854,224: `A>0 1^3078 0^2 1^7304 0^2 1^9`
- left, step 978,991,991: `D>0 1^2979 0^2 1^8943 0^2 1^18`
- right, step 944,977,144: `1^2980 0 1^2239 0 1 0^2 1^6714 0 1 A>0`
- right, step 978,819,074: `1^2980 0 1^2239 0 1^1680 0^4 1^5035 0 1 A>0`

## Pages

- [`pages/holdouts/1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB/explainer.html`](../../pages/holdouts/1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB/explainer.html)
- [`pages/holdouts/1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB/proof-status.html`](../../pages/holdouts/1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB/lean/check.sh
```
