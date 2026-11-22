# The closed (P, Q) map, and the search for congruences that miss the halting lines (22 November 2026)

Tool: `pqmap.py` (this folder). It reads a class certificate (`classes_mod2.json.gz`, the 185-class certificate of
1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD, or the 7,030-class one of the mirror machine
1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA). Everything here is computed from the certificate by programs; the
certificate itself is replayed in Lean (`lean/Lines.lean`, `halts_iff_lines`), the map and the tests below are not.

## The map

Of the 185 classes, 160 have one free count P and, for large P, exactly one piece (`P = a + 2y -> b + 6y`, so
`P -> 3P + c`, or into a class with two counts). So the run through them is determined, and `pqmap.py` composes those
chains away. What is left is a closed map on **16 classes with two counts (P, Q)**, 10 tape shapes, with
**2,313 pieces**. Each piece is affine on a lattice cone `(P, Q) = s(x), x >= 0`. Most pieces (2,268) are
lower-dimensional: one count fixed (often P = 39 after a reset, or a small Q), or the strip `Q = 3P + c` for one
small c. The 45 generic (two-dimensional) pieces are listed below, with the image written in (P, Q).

Checks (`pqmap.py validate`): along the exact run from blank tape, every step of the reduced map equals the composed
node map: 99,226 steps for this machine (first 10^5 nodes), 299,902 for the mirror machine (first 3·10^5 nodes),
0 mismatches.

In ratio terms (r = Q/P) the generic pieces are the continued-fraction-like moves of the README:
`(8P - 19, Q - 3P + 9)` is r -> (r - 3)/8, `(4P - 13, Q - P + 5)` is r -> (r - 1)/4, `(4Q + 19, P - Q - 10)`
is r -> (1 - r)/(4r), and the pieces `(39, 9P + 5Q - 14)` reset P to 39 and put everything into Q.

**The halting pieces.** Only in S7 (shape A, P and Q odd) and S14 (shape B, P and Q odd), and only on the lines:

    S7  = A:  (27 + 2x, 65 + 6x) and (21, 47), (23, 53), (25, 59)                 that is Q = 3P - 16, P odd >= 21
    S14 = B:  (29 + 2x, 63 + 6x) and (21, 39), (23, 45), (25, 51), (27, 57)       that is Q = 3P - 24, P odd >= 21

The neighbouring strips `Q = 3P - 16 ± 2k` are ordinary pieces that go on to other classes.

## Congruences: none excludes the lines

A congruence argument would be a set S of (class, P mod m, Q mod m) that contains the start, is closed under the
map, and contains no residue of a halting piece. Two tests, both negative:

1. **Inductive residue sets** (`pqmap.py cong`). For each m the smallest closed set of (class, counts mod m)
   containing the start is computed exactly (every piece, every value of its variables mod m). For every
   m = 2 ... 64 it contains a halting piece. Same for the mirror machine (7,030 classes) for m = 2 ... 24. So no
   closed congruence set with such a modulus exists. The sets mod 2^k are small (431 states mod 8, 7,914 mod 128,
   against about 270,000 possible), so the map has real 2-adic structure, but it does not separate the lines.
2. **The orbit itself** (`pqmap.py orbit`, then `lines`), which is stronger: it rules out any condition mod m,
   closed or not. The exact node map from the first node (count 35 at step 20,791) for 2,051,711 nodes (900 s,
   counts up to 2,954 digits) visits S7 1,819 times and S14 90 times, never on a line
   (closest: |Q - 3P + 16| = 301,636 at S7). But for **every m < 343** some S7 visit has Q - 3P + 16 = 0 mod m
   (the first misses, 343, 461, 539, ..., are what 1,819 random samples give). The 2-adic valuation of
   Q - 3P + 16 at S7 is geometric (1: 328, 2: 168, 3: 92, ... in the first 671 visits). So the orbit meets the
   A line modulo every small modulus; any congruence invariant would have to use a modulus of at least 343, and
   nothing suggests one.

**The mirror machine 1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA.** Its certificate has no cycle rules, so its
reduced map is fine-grained (1,319 classes with two or three counts, 1,885 pieces, steps like (P, M, Q) ->
(P + 2, M, Q - 2)); the only halting piece is the class `00001101 (1000)^P 101110001000100010001000100010001010100001
(1000)^Q 101000000101` with Q = 20 exactly, the bottom of the ladder through Y(P, M, Q) whose line is
Q = 3M - 1. `pqmap.py orbit` jumps repeated cycles exactly (a cycle of pieces is applied k times at once, k the
largest for which the last cycle still uses the same pieces; piece domains are convex, so all between do too) and
reaches 3.9·10^361 nodes in 900 s, with the same Y visits as the plain node map over its first 3·10^6 nodes. The Y
classes on which Q - 3M + 1 can be 0 (M and Q of different parity) are entered 456 times, never on the line
(closest 10,704). For **every m < 67** some visit has Q - 3M + 1 = 0 mod m. So, as for this machine, no congruence
with a small modulus keeps the run off the line.

## What this leaves

The question is a pure orbit question for an explicit two-register map with 45 generic pieces: does
(class, P, Q) ever land exactly on one of two lines? Congruences do not decide it; the README's polyhedra search
found no inequality invariant either. Halting would need the continued-fraction-like expansion of Q/P to end exactly
on the line, and the distance to the line behaves like a random large number.

## Reproduce

```sh
D=holdouts/1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD/py/closure
E=holdouts/1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA/py/closure
python3 $D/pqmap.py table $D/classes_mod2.json.gz                  # the map (this file's table), seconds
python3 $D/pqmap.py validate $D/classes_mod2.json.gz 100000 0 35    # 40 s
python3 $D/pqmap.py validate $E/classes_mod2.json.gz 300000 0 21    # 3 s
python3 $D/pqmap.py cong $D/classes_mod2.json.gz 0 35 $(seq 2 64)   # about 5 minutes
python3 $D/pqmap.py cong $E/classes_mod2.json.gz 0 21 $(seq 2 24)   # about 15 minutes
cd /tmp && python3 $OLDPWD/$D/pqmap.py orbit $OLDPWD/$D/classes_mod2.json.gz 0 35 900 87 164 \
  && python3 $OLDPWD/$D/pqmap.py lines x orbit.json.gz 87:-3,1,16 164:-3,1,24
```

## The generic pieces

`(start counts) -> target (target counts in the start counts)`. Shapes: A = `00001 (1000)^P 10100001101000
(0001)^Q 01000000101` (S0, S7), B = `00001 (1000)^P 101000010000001011 (1000)^Q 101000000101` (S5, S14),
C = `00001 (1000)^P 1010000100001 (1000)^Q 101000000101` (S1, S12); the others are written out.

```
16 classes with two or more counts, 2313 pieces
generic piece: start counts as affine forms in x0, x1, ... >= 0 -> target class (target counts in the start counts)

S0 = class 8  00001 (1000)^n 10100001101000 (0001)^n 01000000101  parities [1, 0]: 289 pieces, 6 generic
    (51+2*x0+2*x1, 48+6*x1) -> S0 (39, 81*P + 45*Q + 13)
    (29+2*x0, 102+6*x0+6*x1) -> S1 (8*P - 19, -3*P + Q + 9)
    (43+2*x0+2*x1, 46+6*x1) -> S2 (8/3*Q + 37/3, P - 1/3*Q - 23/3)
    (29+2*x0, 100+6*x0+6*x1) -> S1 (8*P - 19, -3*P + Q + 9)
    (49+2*x0+2*x1, 50+6*x1) -> S3 (8/3*Q + 83/3, P - 1/3*Q - 34/3)
    (29+2*x0, 98+6*x0+6*x1) -> S1 (8*P - 19, -3*P + Q + 9)

S1 = class 16  00001 (1000)^n 1010000100001 (1000)^n 101000000101  parities [1, 0]: 151 pieces, 2 generic
    (57+2*x0+2*x1, 26+2*x1) -> S4 (4*Q + 19, P - Q - 10)
    (37+2*x0, 52+2*x0+2*x1) -> S5 (4*P - 13, -P + Q + 5)

S2 = class 23  00001 (1000)^n 10100001 (1000)^n 1010000001011000101  parities [1, 0]: 211 pieces, 2 generic
    (63+2*x0+2*x1, 34+2*x1) -> S6 (4*Q + 19, P - Q - 8)
    (37+2*x0, 56+2*x0+2*x1) -> S7 (4*P - 5, -P + Q + 2)

S3 = class 38  00001 (1000)^n 10100001 (1000)^n 1010000100001  parities [1, 1]: 36 pieces, 1 generic
    (31+2*x0, 31+2*x1) -> S9 (3*Q + 20, P - 11)

S4 = class 52  00001 (1000)^n 10100001 (1000)^n 10100001000000101  parities [1, 1]: 136 pieces, 2 generic
    (57+2*x0+2*x1, 29+2*x1) -> S6 (4*Q + 17, P - Q - 7)
    (31+2*x0, 51+2*x0+2*x1) -> S7 (4*P - 3, -P + Q + 1)

S5 = class 62  00001 (1000)^n 101000010000001011 (1000)^n 101000000101  parities [1, 0]: 246 pieces, 6 generic
    (43+2*x0+2*x1, 38+6*x1) -> S2 (8/3*Q + 59/3, P - 1/3*Q - 31/3)
    (29+2*x0, 92+6*x0+6*x1) -> S1 (8*P - 33, -3*P + Q + 17)
    (49+2*x0+2*x1, 42+6*x1) -> S3 (8/3*Q + 35, P - 1/3*Q - 14)
    (29+2*x0, 90+6*x0+6*x1) -> S1 (8*P - 33, -3*P + Q + 17)
    (51+2*x0+2*x1, 40+6*x1) -> S0 (39, 81*P + 45*Q - 5)
    (29+2*x0, 94+6*x0+6*x1) -> S1 (8*P - 33, -3*P + Q + 17)

S6 = class 76  00001 (1000)^n 10100001 (1000)^n 101000000101  parities [1, 1]: 121 pieces, 2 generic
    (57+2*x0+2*x1, 27+2*x1) -> S6 (4*Q + 19, P - Q - 9)
    (31+2*x0, 49+2*x0+2*x1) -> S7 (4*P - 9, -P + Q + 3)

S7 = class 87  00001 (1000)^n 10100001101000 (0001)^n 01000000101  parities [1, 1]: 222 pieces, 6 generic
    (47+2*x0+2*x1, 39+6*x1) -> S0 (39, 9*P + 5*Q - 14)
    (27+2*x0, 93+6*x0+6*x1) -> S12 (8*P - 19, -3*P + Q + 9)
    (43+2*x0+2*x1, 43+6*x1) -> S13 (8/3*Q + 37/3, P - 1/3*Q - 23/3)
    (27+2*x0, 97+6*x0+6*x1) -> S12 (8*P - 19, -3*P + Q + 9)
    (45+2*x0+2*x1, 41+6*x1) -> S9 (8/3*Q + 83/3, P - 1/3*Q - 34/3)
    (27+2*x0, 95+6*x0+6*x1) -> S12 (8*P - 19, -3*P + Q + 9)

S8 = class 98  00001 (1000)^n 10100001 (1000)^n 1010000001011  parities [1, 0]: 136 pieces, 2 generic
    (57+2*x0+2*x1, 28+2*x1) -> S6 (4*Q + 19, P - Q - 8)
    (31+2*x0, 50+2*x0+2*x1) -> S7 (4*P - 5, -P + Q + 2)

S9 = class 104  00001 (1000)^n 10100001 (1000)^n 1010000100001  parities [1, 0]: 25 pieces, 1 generic
    (29+2*x0, 28+2*x1) -> S8 (3*Q + 13, P - 9)

S10 = class 110  00001 (1000)^n 10100001 (1000)^n 101000000101  parities [1, 0]: 129 pieces, 2 generic
    (61+2*x0+2*x1, 26+2*x1) -> S0 (39, 9*P + 3*Q - 23)
    (31+2*x0, 48+2*x0+2*x1) -> S0 (4*P - 9, -P + Q + 3)

S11 = class 119  00001 (1000)^n 10100001 (1000)^n 101000000101101  parities [1, 1]: 52 pieces, 1 generic
    (35+2*x0, 31+2*x1) -> S9 (3*Q + 28, P - 15)

S12 = class 129  00001 (1000)^n 1010000100001 (1000)^n 101000000101  parities [1, 1]: 133 pieces, 2 generic
    (59+2*x0+2*x1, 25+2*x1) -> S3 (4*Q + 31, P - Q - 13)
    (35+2*x0, 51+2*x0+2*x1) -> S14 (4*P - 13, -P + Q + 5)

S13 = class 134  00001 (1000)^n 10100001 (1000)^n 1010000001011000101  parities [1, 1]: 156 pieces, 2 generic
    (63+2*x0+2*x1, 29+2*x1) -> S0 (39, 9*P + 3*Q - 14)
    (33+2*x0, 51+2*x0+2*x1) -> S0 (4*P - 5, -P + Q + 2)

S14 = class 164  00001 (1000)^n 101000010000001011 (1000)^n 101000000101  parities [1, 1]: 235 pieces, 6 generic
    (49+2*x0+2*x1, 37+6*x1) -> S0 (39, 9*P + 5*Q - 16)
    (29+2*x0, 91+6*x0+6*x1) -> S12 (8*P - 33, -3*P + Q + 17)
    (45+2*x0+2*x1, 41+6*x1) -> S13 (8/3*Q + 59/3, P - 1/3*Q - 31/3)
    (29+2*x0, 95+6*x0+6*x1) -> S12 (8*P - 33, -3*P + Q + 17)
    (47+2*x0+2*x1, 39+6*x1) -> S9 (8/3*Q + 35, P - 1/3*Q - 14)
    (29+2*x0, 93+6*x0+6*x1) -> S12 (8*P - 33, -3*P + Q + 17)

S15 = class 178  00001 (1000)^n 10100001 (1000)^n 10100000010101  parities [1, 1]: 35 pieces, 1 generic
    (33+2*x0, 29+2*x1) -> S9 (3*Q + 26, P - 13)
```
