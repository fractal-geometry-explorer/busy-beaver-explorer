# 1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC

bbchallenge id 151599. One of the six-state holdouts whose halting from blank tape is open. (group G07).
Family: **two-symbol-pair rewriting system (three states D, E, B on bits) driven by a zig-zag over a block**.
Decision: **open** (no halt in 3·10^7 rounds = 8.39·10^15 steps; the evidence points to an invariant, not found yet).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RE |
| B | 1RC | 0LD |
| C | 1LB | --- |
| D | 1RA | 1LD |
| E | 1RA | 0RF |
| F | 1RE | 0LC |

## What it does

**Read the tape two cells at a time.** Write `0 = 01`, `1 = 11`, `a = 10`, `b = 00` (b is also the blank pair), and
put the head either before a pair (`X>`: state X on its first cell) or after one (`<X`: state X on the second cell
of the pair to its left). From either position the machine leaves the pair after at most 3 steps, so it is a machine
on pairs (`py/pairs.py table`; every macro move is a Lean theorem for every tape, `lean/Pairs.lean`). After the
start-up (the last other move is in round 387) only twelve of the 48 moves are ever used, and these are the whole
machine from then on:

    1 <D  ->  <D 1          0 <D  ->  1 E>
    E> a  ->  0 E>          E> 0  ->  1 E>          E> 1  ->  <B a          E> b  ->  1 B>
    1 <B  ->  <D a          0 <B  ->  1 B>
    B> 1  ->  <D 0          B> a  ->  <D b          B> b  ->  <D 0          B> 0  ->  HALT

Left of the head there are only bits (0, 1); the symbols a and b live only right of the head. Composing the B moves:

    D moving left:   1 <D -> <D 1        0 <D -> 1 E>          (D looks for a 0, sets it, and E starts to the right)
    E moving right:  E> a -> 0 E>        E> 0 -> 1 E>          (E raises every symbol by one: a -> 0 -> 1)
                     1 E> 1 -> <D a a    0 E> 1 -> <D 1 b      (a 1 sends it back, and what it leaves depends on the bit behind)
                     E> b 1 -> <D 1 0    E> b b -> <D 1 0      E> b a -> <D 1 b
                     E> b 0 -> HALT

So **the machine halts iff E ever reads `b 0`**.

**A round.** At the end of a round the tape is `R (0011)^k E>` with blank to the right: a word of bits R (the
*region*) and the block, k copies of `0011` (the 8-cell word 01011111). Then

    E> b b  ->  <D 1 0                                             (2 new pairs at the right end)
    (0011)^k <D  ->  <D (1aab)^k              38 steps a word       (Lean: `sweep_left`)
    ... the head works at the end of R, a real computation in the D/E system above ...
    001 B> (1aab)^n  ->  (1001)^n 001 B>      26 steps a word       (Lean: `sweep_right`)

and E reaches the blank again. Each round adds 4 cells: on average the block gains 0.291 words and R 0.835 pairs.
R is not a counter with digits: it is the trace of the D/E system and looks random, but it is not arbitrary (in
8·10^5 pairs of R after 10^6 rounds the words `100010` and `101010` never occur, nor `0000000`; only 118 of the
128 words of 7 bits occur and 223 of the 256 of 8 bits).

**The work in R is local.** `c/psim.c` runs the pair machine with the two block rules as jumps (exact; step counts
equal to the plain pair machine, which equals the plain machine round by round, `py/pairs.py check`). In 3·10^7
rounds (8,388,105,420,665,431 steps, k = 8,734,830, R = 25,061,030 pairs) there is no halt, and the number of pairs of
R read in a round has a geometric tail:

| pairs of R read in a round | < 8 | < 16 | < 32 | < 64 | < 128 | < 256 | < 512 | < 1024 | < 2048 | < 4096 |
|---|---|---|---|---|---|---|---|---|---|---|
| rounds | 1,984,851 | 6,224,610 | 8,286,816 | 6,165,124 | 4,064,858 | 2,218,468 | 886,379 | 163,503 | 5,382 | 7 |

The deepest round read 2,731 pairs, while R grows by 0.835 pairs a round: the left half of R is never read again
(between rounds 8,388,608 and 16,777,216 the lowest pair read is number 6,998,950 of 14 million). The earlier
estimate of a heavy tail (first pass, from cells that *differ* between visits) was wrong: the depth is about
1,500 pair moves a round on average, independent of the round.

**Evidence for an invariant.** A halt needs `b 0` right of the head. Following the moves back, the first step to it
is E reading a 1 that is followed by `0` or `b` *with a 0 behind it* (`0 E> 1 0` gives `<D 1 b 0`, then `<D a a b 0`, and the next time E
comes through `a a` it reads `b 0`). Counted over the 3·10^7 rounds:

| E reads 1, next symbol is | 0 | 1 | a | b |
|---|---|---|---|---|
| bit behind E is 0 | **3** (rounds ≤ 7) | 680,762,334 | 558,856,010 | **0** |
| bit behind E is 1 | 950,895,256 | 1,334,853,230 | 972,641,756 | 2,248,774,623 |

and `E> b` was followed by `0` never, by `1` 627,111,079 times, by `a` 1,009,156,276 times and by `b` 353,784,173
times. A dangerous situation that arose with a fixed probability would have been seen billions of times; it has
not occurred once after round 7. So the configurations of the D/E system reached from blank tape satisfy a
structural constraint that excludes the halt, and the machine very probably never halts; the constraint is not
known. It is not a local one: n-gram closed position sets on the pair machine (windows of up to 9 pairs on each
side, seeded with the steady-state words) and the direct finite-automaton closure with "last n pairs" automata
(n ≤ 5) all let the halt in; so do n-gram closed sets over run-length coded tapes (windows of up to 7 maximal
runs a side, counts capped at 2 to 12), which can express "any number of a's", from blank tape and from the tape of
round 398. One reason is plain: every such closure also contains the configurations with the head deep in the old
part of the region or at the left end of the tape, where the start-up left other words; that the head stays out of
there is, so far, only a statistical fact.

## Status

Open.

- **Kernel:** `step_none_iff`, `blank_runs_kernel` (`lean/Blank.lean`); `sweep_left`, `sweep_right`
  (`lean/Rules.lean`, from `py/rules.py`); the 41 macro moves of the pair machine for every tape (`lean/Pairs.lean`,
  from `py/pairs.py lean`). **native_decide:** `blank_runs_native` (10^7 steps).
- **Trusted:** the pair machine equals the plain machine at every round, tapes and step counts (`py/pairs.py check`,
  398 rounds, 3·10^6 steps); `c/psim.c` with and without the block jumps gives the same step counts; no halt in
  3·10^7 rounds = 8,388,105,420,665,431 steps; the last macro move outside the twelve of the D/E/B system is in
  round 387; the tables above.
- **Heuristic:** it never halts (the precursor of the halt does not occur in 3.2·10^9 opportunities).
- **Open:** the invariant of the D/E system that excludes `0 E> 1 {0, b}` (and so `E> b 0`), and with it the proof.

## Next steps

* Find the language of the words right of the head. They are built by only two processes: D moving left turns
  `0 1^m` (m ≥ 1) into `a a 1^(m-1)`, and E's returns (`<D a a`, `<D 1 b`, `<D 1 0`). The halt needs
  `0 1 1 <D` in front of `0` or `b` with no `b` to eat the two a's (`E> b a -> <D 1 b`), so the invariant has to say
  when a `b` stands in front; a context-free or counting description may be needed (regular n-gram ones fail).
* With the invariant: a closed-language proof on the pair machine (`lean/Pairs.lean` has the moves), started from the
  configuration after round 387, which `native_decide` reaches from blank tape.

## Pages

- [`pages/holdouts/1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC/explainer.html`](../../pages/holdouts/1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC/explainer.html)
- [`pages/holdouts/1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC/proof-status.html`](../../pages/holdouts/1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC/lean/check.sh
cd holdouts/1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC
python3 py/pairs.py table && python3 py/pairs.py check                   # the pair machine, against the plain machine
python3 py/pairs.py ctable | diff - c/tab.h && python3 py/pairs.py lean | diff - lean/Pairs.lean
python3 py/rules.py | diff - lean/Rules.lean
gcc -O2 -o /tmp/psim c/psim.c && /tmp/psim 1000000        # 10^6 rounds, 10^13 steps, about 12 s; 30000000: 10 minutes, 1 GB of address space
/tmp/psim 20000 0 | grep ^end; /tmp/psim 20000 1 | grep ^end           # without and with the block jumps: same steps
```
