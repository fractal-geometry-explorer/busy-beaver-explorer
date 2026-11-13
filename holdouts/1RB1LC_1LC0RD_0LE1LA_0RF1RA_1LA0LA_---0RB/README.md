# 1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB

bbchallenge id 134427. Halting from blank tape is open; the macro rule moves a quarter of one block into another, a 3/4 map that branches on residues mod 4 (Collatz-like, not yet written exactly).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LC |
| B | 1LC | 0RD |
| C | 0LE | 1LA |
| D | 0RF | 1RA |
| E | 1LA | 0LA |
| F | --- | 0RB |

## The event map (proved, exact)

At an **anchor** `Y 1^m C> 0 1^c Z` (state C on a single 0, m ones on its left, c ones on its right) the machine reaches the next anchor by one of these rules, each proved in `lean/Events.lean` for every block length and every surrounding tape:

| event | when | effect |
|---|---|---|
| split | m even, ≥ 4, three or more 0s left of the block | `Y 0 0 0 1^m C> 0 1^c` → `Y 1^(m/4) 0 0 0 1^(m%4) C> 0 1^(c+3(m/4))` |
| odd | m odd, ≥ 3, Y not empty | `Y 0 1^m C> 0 1^c` → `Y 1^(m-2) C> 0 1^(c+3)` |
| fold | m odd, ≥ 3, at the left end of the tape | `1^m C> 0 1^c` → `1 C> 0 1^(c+3(m-1)/2)` |
| shift | m even, too few 0s on its left for a split | `Y 0 1^m C> 0 1^c` → `Y C> 0 1^(m-1) 0 0 1^c` |
| two | m = 2 | `Y 0 0 0 1 1 C> 0 1^c` → `Y 1 1 0 0 C> 0 1^(c+1)` |
| zero, one, oneE, oneO | m = 0 or 1 | the remainder is handed across the gap; in most cases the head runs right behind a carrier `0 1`, which passes blocks that follow a single 0 and becomes `1 1 1` at the first `0 0` or at the end of the tape (here also `zeroE`, `zeroO` for a single 0 with a block behind it) |

Theorems: `event_sem` (an event is a run of the machine), `F_sem` and `halts_iff` (the machine halts from blank tape iff the orbit of the map F, an event where one applies and one machine step otherwise, reaches a halting configuration), `events_forever` (if the events alone can be iterated for ever from the first anchor, the machine never halts), and in `lean/Far.lean` `no_halt_kernel` (no halt in the first 10^137 steps, 29,996 events evaluated by the kernel) and `no_halt_native` (no halt in the first 10^13275 steps, 2,999,995 events, compiled).

Shape of the run: after a fold the tape is `1 C> 0 1^N`; splits cut the block into pieces (a quarter left, three quarters right, again and again), odd rounds glue the pieces back together, and a fold at the left end turns every 2 ones into 3. Which of these happens depends on the block lengths mod 4 and their parities: Collatz-like, open. A halt needs an anchor that no rule covers (a right block that is too short, or the carrier meeting a lone 1); none occurs in the first 2,999,995 events.

The explainer page replays this map in the browser (rule viewer on the real machine, event-by-event stepper). Its sources are in `holdouts/1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB/explainer/` (`core.js`, `spec.js`, `widget.js`, `build.py` for both machines of the pair); `node holdouts/1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB/explainer/test.js 4e8` checks the JavaScript against the plain machine (every viewer example; the first 467 events of this machine's run).

The sections below are the earlier, partial description (a different phase of the same rounds); the event map above supersedes it.

## What it does

At the moments the head, in A, extends the tape to the right, the tape is two long blocks of 1s with a gap `000`
between them, a few single marks and a tail `0 1`; the right end moves 2 cells each time:

    step 147,381,276   1^1400 000 1^4198 0 1 A>
    step 160,619,690   1^2452 000 1^3148 0 1 A>
    step 168,067,870   1^3239 0 1 000 1^2361 0 1 A>

Most of the time a single 0 **crawls** right through a block of 1s, one cell per 5 steps:

    L 1 1 1 0 C> 1^(n+2) R  ->  L 1^(n+4) 0 1 A> R        (5n+4 steps)

and while a second 0 near the right end steps 3 cells left per crawl, a full round moves about a quarter of
the right block y into the left block: while y ≡ 0, 2 (mod 4), y -> y − ⌈y/4⌉ (4198 -> 3148 -> 2361; 1686 -> 1264
-> 948 -> 711; 2472 -> 1854 -> 1390 -> 1042 -> 781). When y is odd the round ends differently: the left block shrinks
and y grows (2361 -> 5425, 781 -> 2788).

So the macro dynamics is a 3/4-type map with branches on residues mod 4: Collatz-like.

## What is proved

- Lean, kernel (`lean/Rules.lean`, from `py/rules.py`): `crawl`, `a_crawl`.
- Lean (`lean/Blank.lean`, generated): the halting configurations, no halt in 10^4 / 10^7 steps.

## Open

Halting. The round rule above is read off the run (heuristic).

## For later

- Write the round exactly (both residues), as a map on (x, y, marks), check it against all moments of the run, and
  prove its pieces with symtm (the crawl is done).
- Then study the map: does y ever reach a small value in a bad residue?

## Reproduce

```sh
./tokrun 1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB 400000000 a=10,b=1110 R    # the tape at right extensions
python3 holdouts/1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB/py/rules.py > lean/Rules.lean
. /etc/profile.d/lean.sh && holdouts/1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB/lean/check.sh
```

## Pages

- [`pages/holdouts/1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB/explainer.html`](../../pages/holdouts/1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB/explainer.html)
- [`pages/holdouts/1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB/proof-status.html`](../../pages/holdouts/1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB/proof-status.html)
