# 1RB1RD_0RC0RD_0LD1LE_1LC0RB_1LF---_1LA0LE

bbchallenge id 161169. One of the six-state holdouts whose halting from blank tape is open (group G10, family F10).
Family: **two-block bouncer whose exchange is a binary halving cascade, with self-similar restarts**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RD |
| B | 0RC | 0RD |
| C | 0LD | 1LE |
| D | 1LC | 0RB |
| E | 1LF | --- |
| F | 1LA | 0LE |

## What it does

Each time the head steps onto a new cell at the right end in state C (an *event*) the tape is almost always
`(10)^x 0^y`, written (x, y), and the width 2x + y has grown by 4 since the last event. Between two events the head
makes one *pass*: a sweep left, then a sweep right.

**The sweep left** turns the 0 block into pairs: `(10)^x 0^y` becomes `(10)^(x-2) 11 (10)^(y/2+1)` with a separator
`11` (Lean: `sweep_left`).

**The sweep right is a front** that halves every block of pairs it meets. The front is
`(10)^a 0^z [head] (10)^b`: one *cycle* eats two pairs ahead and puts one pair and two 0s behind
(a, z, b) -> (a + 1, z + 2, b - 2), in 28m + 30 steps where z = 2m (Lean: `cycle`, `front_cycle`; `front_cycles`
iterates it k times by induction). Inside a cycle the word `0 1 1 1 0` walks left through the 0s, turning each into
a 1, 13 steps a cell (`fill`), and the 1s are turned back into 0s on the way right. So the front leaves behind half
as many pairs as it ate, plus a block of 0s.

What happens at the end of a block depends only on the parity of b there:

| where the block ends | b odd | b even |
|---|---|---|
| at the separator `11` | **reset**: the 0s behind the front are turned back into pairs and become the block ahead, b = (z + 3)/2, z = -1, a + 1; the block after the separator loses one pair | **cross**: a + 1, z + 4, the front goes on into the block after the separator |
| at the right end | the pass ends: (x', y') = (a + 1, z + 5) | **reset** as on the left, b = (z + 3)/2, z = -1 |

A reset re-reads the 0s as a new, half-size block, so the front can reset several times in a row: on the left
block the counts run b -> (b + 1)/2 while b stays odd (b - 1 is halved each time), on the right block
b -> (b + 2)/2 while b stays even (b - 2 is halved each time). The number of resets is a 2-adic valuation, which is
where the irregular jumps of x come from. The pass starts with the front (2, 1, x - 5) on the left block and
c = y/2 + 1 pairs in the right block.

## The pass map

Put together (`py/passmap.py`, `step`):

```
a, z, b, c = 2, 1, x - 5, y/2 + 1
while b odd:  a += (b-1)/2 + 1;  z += b - 1;  b = (z+3)/2;  z = -1;  c -= 1      # resets on the left block
a += b/2 + 1;  z += b + 4;  b = c - 2                                               # cross the separator
if b < -2: restart (below);  if b in {-2, -1}: (a, z, b) = (a-1, z-2, b+2)          # the same front
while b even: a += b/2;  z += b;  b = (z+3)/2;  z = -1                              # resets at the right end
a += (b-1)/2;  z += b - 1;  (x', y') = (a + 1, z + 5)
```

It agrees with the machine on all 1,396 events from blank tape up to 2·10^10 steps, and on 300 random starts
(x ≤ 400, y ≤ 80) (`python3 py/passmap.py check-blank 800`, `check-random 300`).

## Restarts

When the left block resets more times than the right block has pairs (c < 0 at the crossing, j = -c), the pass
ends differently: the next event is `(10)^X 0^Y0 10 0000` with

    Y0 = 2^j (z - 4) + 1,   X = a - ((2^j - 1)(z - 4) + 2j + 1)/2

(checked on all 542 such starts with x < 1,100, y < 16). `10 0000` is the tape of the run from blank after 13 steps.
What follows is **a copy of the run from blank tape**, played to the right of a wall of X pairs: its events are
exactly the blank run's, while the buffer of 0s between the wall and the copy shrinks by 3 a pass (the copy's left
end creeps 3 cells left each pass). When the buffer runs out, everything depends on Y0 mod 3:

- **Y0 = 0 mod 3**: after k = Y0/3 passes the buffer is 3 and the copy merges into the wall: the next event is
  (X + x, y) where (x, y) is the blank run's (k+1)-th event.
- **Y0 = 2 mod 3**: the buffer reaches 2 and **the machine halts** two passes later.
- **Y0 = 1 mod 3**: the buffer reaches 1 and the wall itself is cut down (to about half, or 3/4) with a new buffer;
  this nested case is not decoded yet.

(`python3 py/passmap.py check-restarts 40` compares the first two cases with the simulator.) So the halting
question is: **does the run ever reach a restart whose buffer is 2 mod 3?** Example halting tapes:
(10)^(2^m+4) 0^(2m-6) halts for every m checked (3 to 9: `py/passmap.py halts 9`); its restart has buffer 5.

## The run from blank, by the model

`c/model.c` iterates the pass map with the restart rules. The first restart is at the 975,986th event,
x = 2,497,092, y = 6 (about 7·10^18 steps): j = 2, wall 2,419,060, buffer 156,069 = 0 mod 3, so it merges after
52,023 passes of the inner copy, giving (2,485,572, 133,026). After that there is no further restart through
4.29·10^10 passes (width 2.2·10^11, roughly 10^32 to 10^33 steps at 0.8 to 1.1 W^2 steps a pass; 15 minutes). This is a model, not a proof: every
rule in it is checked against the simulator on many cases, but only the cycle, the fill and the left sweep are
proved in Lean.

Restarts are rare (y has to be tiny when the left block has many resets in a row), and a restart halts only if its
buffer is 2 mod 3. Whether one ever comes is a question about how often y is small at the same time as x - 5 has a
long run of the right binary digits.

## Status

**Open.** Lean (`lean/check.sh`): the halting configurations, no halt in 10^4 steps (kernel) and 10^7 steps
(`native_decide`); `Rules.lean`: `fill`, `cycle`, `sweep_left` (generated by `lean/rules.py` with
`tools/py/bbtools/symtm.py`); `Front.lean`: `front_cycle` and `front_cycles` (k cycles, by induction). Deciders tried
without success before: `bbtools.ctl` (K = 2..6), `ngramcps` (widths 2..6, `-H 2`, `-H 3`, `-U`).

## For later

- Decode the Y0 = 1 mod 3 restart (the wall is processed by a front of its own) and run the model past it.
- Prove the separator and right-end rules in Lean with `symtm` (they split on parity), then the pass map as a
  theorem by induction on the resets.
- Push `c/model.c` further (it does about 10^9 passes in 20 s; it needs a deeper table of the blank run once a
  buffer passes 3·975,986).

## Reproduce

```sh
gcc -O2 -o c/events c/events.c && python3 py/passmap.py check-blank 800 && python3 py/passmap.py check-random 300
python3 py/passmap.py check-restarts 40 && python3 py/passmap.py halts 9
gcc -O2 -o model c/model.c && ./model 100000000000
. /etc/profile.d/lean.sh && lean/check.sh
```

## Pages

- [`pages/holdouts/1RB1RD_0RC0RD_0LD1LE_1LC0RB_1LF---_1LA0LE/explainer.html`](../../pages/holdouts/1RB1RD_0RC0RD_0LD1LE_1LC0RB_1LF---_1LA0LE/explainer.html)
- [`pages/holdouts/1RB1RD_0RC0RD_0LD1LE_1LC0RB_1LF---_1LA0LE/proof-status.html`](../../pages/holdouts/1RB1RD_0RC0RD_0LD1LE_1LC0RB_1LF---_1LA0LE/proof-status.html)

## Accelerated run

Trusted computation: `tools/c/rleaccel.cpp` (compiled port of `tools/py/bbtools/rleaccel.py`, checked against it by
`tools/tests/test_rleaccel_cpp.py`), blocks of 2, runs from blank tape without a halt to 8.52·10^13 machine steps (exact; tape:
115,942 cells). It ran about 30 minutes, resumed from a checkpoint after interruptions, so its macro count
(15,750,000,000) differs from an uninterrupted run's. Command: `g++ -O2 -o rleaccel tools/c/rleaccel.cpp && timeout 1800 ./rleaccel 1RB1RD_0RC0RD_0LD1LE_1LC0RB_1LF---_1LA0LE 2 1000000000000000 run.ck 300`.
