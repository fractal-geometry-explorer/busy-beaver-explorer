# 1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA

bbchallenge id 129887. One of the six-state holdouts whose halting from blank tape is open (group G07, family: **recursion on words over two 3-cell tokens (a stack of frames; a halt needs a rare coincidence when a visit reaches the right end)**).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 1LC | 0LF |
| C | 1RA | 1LD |
| D | 1LB | 1LE |
| E | 0LC | 0RD |
| F | --- | 0RA |

## What it does

The tape has three parts. At the left (growing) end sits a **periodic block**, `(1^5 0 1^2 0)^k` (at other times
`(1^8 0)^k`, another word of 9 cells). Each visit of the left end adds three
cells to it, one copy every three visits. To its right lies a **disordered middle**, runs of 1s of lengths
divisible by 3 separated by `0` and `110`; it keeps changing and eats the periodic block from the inside: the
block grows steadily, then at rare moments is swallowed almost entirely (14 times in the first 10^9 steps, last
at step 401,140,791, when at least 749 copies went at once). At the right, a short end region stopped growing early.

Snapshot at step 999,899,483 (`a = 111110110`, `b = 110`): `0 1 b a^2938 b^4 a b^11 1^6 b 1^3 b 1^3 b 1^9 a ...`

## Status

**Open, and now for a different reason.** The whole behaviour is decoded: an exact model on words (a stack of
frames, `py/model.py`, twelve transitions) reproduces the run from blank tape step for step, and in that model the
halt is one explicit case. The earlier hope, "every word over 110 and 111 leads to such a word again, so it never
halts", is **false**: on the 19-token word `b c c c b b b b c c b b b b b b c b c` the machine halts on its 6,323rd
step (Lean, kernel: `lean/HaltingWord.lean`). The run from blank tape has not halted in its first **2,097,152 visits =
13,274,338,602,371 steps** (`c/wrun.c`, the model run exactly; identical to a direct run at all 74,198 visits of the first
2·10^10 steps). Whether it ever halts depends on what happens at the rare visits that reach the right end of the
tape (31 so far, the last one visit 1,095,353): each is a small chance of a halt (a few in a thousand, judging by
random words), and they keep coming about once or twice each time the number of visits doubles. So the machine
probably halts, but only after something like 2^150 visits or more, which no run will reach; and there is no
invariant in sight that would prove the opposite.

* **Lean (kernel)**: `lean/HaltingWord.lean`: `haltingWord_halts`, `word_can_halt` (the conjecture is false).
* **Lean (kernel)**: `lean/Sim.lean`: **the machine follows the model.** The model is a Lean function `mstep` on
  states (a list of frames and RET, Z or CALL with a word), `den` gives the tape of a state, and `mstep_next`: when
  `mstep s` is a state `s'` with a step count k, the machine goes from the tape of `s` to the tape of `s'` in k
  steps; `mstep_halt`: when `mstep s` is the halt, the machine halts; `mrun_sound`, `blank_runs_of_mrun`: a run of
  the model from `RET(1, c)` is a run of the machine from blank tape. As a check of the chain, 20,000 transitions
  (130,661 steps) are run by the kernel and 5,000,000 (33,257,365 steps) by `native_decide`; `py/model.py` counts the
  same steps.
* **Lean (kernel)**: `lean/ModelWords.lean`: frames and words defined in Lean, and every line of the model's
  transition table as a theorem about the machine, at any depth of the stack: `ret_stride`, `ret3`, `ret2`,
  `ret2_pop`, `ret1`, `ret1_pop`, `ret1_one`, `ret1_halt`, `z_call`, `z_call_end`, `call_word`, `call_end` (with
  `ret3_bottom`, `ret2_bottom`, `ret1_bottom` for the blank tape at the bottom of the stack), `blank_to_model` (two
  steps from blank tape the machine is in `RET(1, c)`) and `visit_of_ret1`.
* **Lean (kernel)**: `lean/Model.lean`: the tape moves behind them for every repeat count and any surrounding tape
  (`stride`, `stride1`, `stride_q2`, `ret1_fill`, `ret1_split`, `z_turn`, `a_run`, `call_cb`, `call_c`, `b_eat`), one
  for each transition, and `halt_pattern` (`L 0 1 0 C>1 R` halts on its fourth step).
  `lean/Shifts.lean`, `lean/Route.lean`, `lean/Blank.lean` as before.
* **Trusted**: `py/model.py`, `c/wrun.c`: the same model as programs (not extracted from Lean). Checked against direct runs: the next word and the exact step
  count of the visit on every one of the 131,070 words of at most 16 tokens (`py/model.py all 17`), the halts of the
  19-token words, and the run from blank tape: word (hash) and step number of each of the 74,198 visits of the first
  2·10^10 steps (`c/dvis.c` against `c/wrun.c dump`, byte-identical output).
* **Trusted**: no halt in the first 2,097,152 visits (13,274,338,602,371 steps), by `c/wrun.c run`. Earlier: 10^12 steps direct.
* **Trusted**: no word of at most 18 tokens halts during its visit; two of 19 tokens do, one of 20, five of 21,
  eleven of 22 (`c/wrun.c enum`).
* **Heuristic**: the halting chance per visit that reaches the right end, and the rate of such visits (below).
* **Open**: whether the run from blank tape halts.

## Fifth look: can whole cascades be skipped? (no way found; what there is, and what stands in the way)

This pass looked for an accelerator: closed forms for many visits at once on words with large exponents, as for
the ladder machine `1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB`. **None was found, and the measurements below say why
one of that kind cannot exist for this run.** Nothing here changes the status: open.

**One recursion.** Unfolding F once in the clean recursion gives a recursion for T alone, and the visit is T:

    T(b Y)            = c c Y
    T(c^j b c^i b Z)  = c b T^(j-1)( b^(i+1) T(Z) )         (j >= 1, i >= 0)
    F(b W)            = b T(W)            T(a Z) = a T(Z)   (a = c b b)

(`py/trec.py rec 20000`: against the model on random words). Behind four b's, three visits hand exactly one T on:
`T^3(b^4 c^m b Y) = a b^(4+m) T(Y)`.

**The one closed form: a run of b is a binary counter.** Write D(k) for the binary digits of k, lowest first, each
digit doubled, 0 as `bb` and 1 as `cc`. Then for every k and every word W

    T^3( b^4 D(k) b^r W ) = a b^4 D(k+1) b^r' W ,      so      T^(3k)( b^n W ) = a^k b^4 D(k) b^(n-4-2 len(k)) W

(r' = r minus 2 if k+1 has one more digit than k; checked for all k < 100,000, `py/trec.py counter 100000`). Three
visits are one increment; a run of n b's lasts for about 2^((n-4)/2) increments and costs O(1) transitions each. This
is the "nested counter" of the third look, and it is as far as closed forms go: the b's are the zeros of the counter,
and the words of the run are not runs of b.

**What stands in the way.**

* *The word has no short description.* The word of visit V is `b a^k R`. For R (`py/entropy.py`):

      visit    tokens  a-block k  tokens of R  runs of equal letters  outside repetitions u^n  LZMA, bits
      1,024    1,619   52         1,462        741                    976                      2,560
      4,096    7,105   276        6,276        3,093                  4,053                    8,736
      16,384   19,705  2,425      12,429       6,175                  6,359                    13,600
      65,536   74,343  10,919     41,585       20,466                 26,419                   48,896
      131,072  142,780 32,764     44,487       22,353                 29,030                   52,416
      262,144  274,454 9,988      244,489      131,445                149,599                  86,272

  ("outside repetitions": tokens left when every u^n with |u| <= 40, n >= 4 is taken out.) R has about as many runs
  as half its tokens, as coin flips would, and a general-purpose compressor needs tens of thousands of bits for it,
  more at every doubling (roughly like V^0.6). Exponents do not help: the only large one is k. A ladder of levels
  (the method of the other machine) has a state of a few numbers per level; this word is not of that kind.
* *A visit that reaches the right end rewrites the whole word.* The words before and after visits 32,497, 50,841,
  113,145 and 118,809 have their last token in common and nothing more (visit 231,897: 12 tokens;
  `py/entropy.py WRUN rewrite`). So the state at the moments that matter is the whole word, every time.
* *The work sits in a few enormous visits.* The calls inside a visit behave like a branching process at its
  critical point (fourth look). The model takes 1.1·10^9 transitions up to visit 131,072 and 3.4·10^10 up to visit
  1,048,576, and almost all of them in a few visits (`c/wrun.c costs 400000 3000000`: up to visit 400,000 the 98
  visits with at least 3 million transitions take 5.1 of the 5.4 billion; visit 318,209 alone takes 1.2 billion).
* *The heavy visits follow a clock, but that does not make them cheap.* The words after the collapses of the block at
  visits 32,777 and 232,177 start with the same 23,257 tokens (`py/entropy.py WRUN prefix 32778 232178`): `c^4 (b c
  c)^92`, 743 tokens, and then a word U of 36 tokens (`c b c a b b a c c a c a b c^5 a b c^6`) repeated, 617 times
  after the first collapse and 5,455 times after the second (a collapse turns the block `a^K` into `(b c c)^K`, here K
  = 7,796 and 66,372, and U^(K/12) is what is left of that 280 visits later, when the new block of 92 collapses in
  turn). In the 167,823 visits that follow, all 40 visits of the first stretch that take at least 3 million
  transitions have a partner in the second stretch **at the same distance from the collapse**, and 25 of the 40 take
  exactly the same number of transitions (4,903,235 at distance 106,720, for example); the other 15 are the deepest
  ones, which run past the common part. The three visits of the first stretch that reached the right end (50,841,
  113,145, 118,809, at distances 18,064, 80,368 and 86,032) are among these: in the second stretch the visits at the
  same distances (250,241, 312,545, 318,209) take 56, 66 and 1,225 million transitions and stop inside the longer
  word. The clock has a visible first wheel: of the 559 visits between visits 3,266 and 400,000 that take at least
  100,000 transitions, 519 come when the block has k = 4 mod 8 copies of `a` (22 at k = 7, 18 at k = 0), and so do all
  15 right-end visits between visits 1,169 and 400,000 (`c/wrun.c costs 400000 100000`): behind `a^k b^4` the word is seen to
  go through a cycle of eight increments (24 visits) and to hand one T on to the rest at k = 4 mod 8; what the rest
  does with it is the chaotic part. So *when* a deep visit comes is decided near the front of the word and repeats
  from collapse to collapse; *whether* it reaches the right end, and what the cascade there does, depends on
  everything behind. On the common part the run is one fixed sequence of words, but that sequence is itself the
  chaotic object (its visits are the heavy ones above).

**What it means for the estimate.** A method that follows the run exactly has to carry the word. At the rate of the
table the word of visit 2^150 has more bits than any memory holds, and each right-end visit reads all of it. So the
estimate "it probably halts near visit 2^150" cannot be checked by running, with or without acceleration; a decision
would have to come from a property of the frames at the right end that does not need the word, and none is known.

## Fourth look: the complete recursion is a stack machine

Tokens `b = 110`, `c = 111`. During a visit the tape is a **stack of frames** followed by an active part:

    0^inf [1^n1 0^z1] [1^n2 0^z2] ... [1^nk 0^zk]   +   RET(q, v)  or  Z(v)  or  CALL(m, X)

* `CALL(m, X)`: `1^m B> X`, the head goes right into the word X (written `1 1 x0, 1 1 x1, ...`, then blank);
* `RET(q, v)`: `1^(q-1) C>1 :: v`, the head comes back, on the q-th cell right of the top frame; `:: v` is the word v
  in the other phase: `v0, 1 1 v1, 1 1 v2, ...` (bit 0 for b, 1 for c);
* `Z(v)`: `C>0 :: v`, the head on the last zero of the top frame.

A frame is what a call left behind: n ones and z zeros. Each time the returning head finds three zeros there it
fills them and **runs one whole visit on the word to its right**, as it does at the left end of the tape; this is
how a visit calls visits inside visits. The transitions (machine steps in brackets):

    RET(q, v), q >= 4      -> RET(q-3, b v)                                             [5]
    RET(3, v)              -> Z(b v)                                                    [5]
    RET(2, v)              -> Z(b v) with one zero less; or, z = 1: pop, RET(n, b v)    [3]
    RET(1, v), z >= 3      -> Z(c v) with two zeros less                                [3]
    RET(1, v), z = 2       -> pop the frame (n, 2): RET(n, c v)                         [3]
    RET(1, v), z = 1       -> pop (n, 1); n >= 2: push (n-2, 1), CALL(1, v)             [5]
                              n = 1: THE MACHINE HALTS (tape 0 1 0 C>1)                 [4]
    Z(c^a b X)             -> one zero less, CALL(3a+2, X)                              [3a+2]
    Z(c^a), a >= 1         -> one zero less, CALL(3a, empty)                            [3a]
    CALL(m, c^j b Y)       -> push (m-1, 3j+2), RET(1, c Y)                             [9j+7]
    CALL(m, c^j), j >= 1   -> push (m-1, 3j), RET(1, c)                                 [9j+1]
    CALL(m, empty)         -> RET(m, c)                                                 [1]

(A frame whose zeros run out gives its ones to the next CALL; a frame pushed with no ones, m = 1, adds its zeros to
the frame below.) The blank tape on the left is the bottom frame with infinitely many zeros; a *visit* is `RET(1, v)`
on the empty stack (the tape `0^inf C>1 :: v`), two steps before the head stands in B on a blank cell with blank
tape on its left and the word v on its right. The run from blank tape is `RET(1, c)` at step 2. During a visit the
left end of the tape can move to the right (a frame at the bottom is used up), so a visit is not always "a new
cell on the left"; in the first 2·10^10 steps of the run it always is.

In words: a call wipes out the block of c's it meets and the b behind it (3j + 2 zeros, a new frame) and turns
back at once; back at the zeros it fills three of them and calls again, now on what follows the b
(`CALL(m, c^j b c^i b Z)` leads to a frame with 3j − 1 zeros and `CALL(3i+8, Z)` in 9j + 3i + 18 steps), and
`CALL(m, b R)` leads to `RET(m−1, c c R)` in 10 steps.

**The clean case.** As long as no call reaches the right end of the word (the lines `Z(c^a)`, `CALL(m, c^j)` and
`CALL(m, empty)`), every m is 2 mod 3 and every frame has n = 1 mod 3 and z = 2 mod 3: the head comes back to a frame
(z − 2)/3 + 1 times, the last time to pop it, RET always comes back in phase (q = 1 after the strides), and the
model is a recursion on words alone:

    F(c^a b X)  = b^(a+1) T(X)          the visit on a word (RET(1), Z, CALL(3a+2, X))
    T(c^j b Y)  = c F^j(c Y)            the call: j visits inside the visit; for j = 0, T(b Y) = c c Y

(so `T(c^j b c^i b Z) = c F^(j-1)(b^(i+2) T(Z))`). The old rules (1) to (3) are the cases j = 0, 1, 2 with a = 0;
the undecoded rule (4) was j ≥ 3 and the right end. `a = c b b` is j = 1, i = 0: `T(a Z) = a T(Z)`, the periodic
block passes every visit on (`py/model.py rec 20000`: the recursion against the model on random words).
In this case **no halt is possible** (it needs a frame with n = 1 and z = 1, and here n is 4 or more). The word
behind the block looks random: in one long visit the pairs (j, i) of the 1.4·10^8 calls came with frequencies 2^−(j+i) to three digits, as for independent
fair bits, so a call makes on average one visit (j, with probability 2^−(j+1)): a critical branching process, which is why a
few visits are enormous (one of them, visit 318,209, took 1.2·10^9 model transitions) and why the collapses of the
block look erratic.

**The right end.** A call that runs off the word (`CALL(m, empty)`) comes back out of phase: m = 0 or 1 mod 3, RET
ends with q = 2 or 3, zeros are eaten one or two at a time, frames with any n and z appear, and the cascade (tens
of thousands of out-of-phase transitions inside one visit) goes on until every frame is used up. The halt is the
case "RET(1) on a frame with one 1 and one zero". Frames with a single 1 are left by every `CALL(2, c^j b Y)`
(3j + 2 zeros); for j = 0 the frame is popped at once, for j ≥ 1 the head comes back to it j more times, and a halt
is such a frame whose zeros got out of phase. `c/wrun.c` reports these later returns as `near miss`: twelve in the
first 2 million visits of the run (seven frames), always with 2, 5 or 8 zeros left, that is, in phase.

## The conjecture "words lead to words" is false

`c/wrun.c enum L` runs the first visit on every word of L tokens. None of the 524,286 words of at most 18 tokens
halts (and each leads to a word again), but

    b c c c b b b b c c b b b b b b c b c      halts on step 6,323
    b c c c b b c b b c c b b b b b b b c      halts on step 7,941

(19 tokens; both confirmed by direct simulation, the first also by Lean's kernel, `haltingWord_halts`). One word of
20 tokens halts, 5 of 21, 11 of 22. Random words of 1,000 tokens run for 300 visits: 35 of 20,000 halt, among 20,230
visits that reached the right end (`c/wrun.c mc 7 20000 1000 300`). So a proof for the run from blank tape cannot
come from the alphabet of the tape; it would have to control the frames at the right-end events of this one run.

## The run from blank tape

`c/wrun.c run` is the model with words and frames run-length coded (a third letter `a = cbb`: a call on `a^k`
and the return through its k frames are one transition each) and exact step counts.

    visit      step                 tokens     visits that reached the right end so far
    1,024      8,617,539            1,619      15
    16,384     830,873,099          19,705     23
    131,072    81,202,967,563       142,780    28
    262,144    307,011,171,415      274,454    30
    1,048,576  5,119,454,802,255    1,060,886  30
    2,097,152  13,274,338,602,371   2,110,209  31

The right end was reached in visits 1, 2, 5, 6, 42, 72, 88, 188, 296, 344, 456, 568, 640, 865, 953, 1169, 1281, 2257,
2369, 2481, 3265, 8993, 9105, 32497, 32777, 50841, 113145, 118809, 231897, 232177 and 1095353. The cost of the model is
dominated by the few enormous visits, about (visits)^2 transitions in all, so this run cannot be pushed much
further; a direct run needs about (visits)^2.1 steps.

## Why it probably halts, and why no run will show it (heuristic)

* Visits that reach the right end keep coming, about 1.5 for each doubling of the number of visits since visit 1,000
  (the list above).
* A halt needs the returning head to meet a frame with a single 1 at a moment when that frame has one zero. In the
  run it met such a frame 12 times (the near misses above, in 4 of the 31 right-end visits), each time with 2, 5 or 8
  zeros.
* Random words (`c/wrun.c mc`): of 3,000 words of 10,000 tokens, 1,000 visits each, 5 halted, with 1,287 right-end
  visits and 583 such meetings (seed 11); of 20,000 words of 1,000 tokens, 300 visits each, 35 halted, with 20,230
  right-end visits and 2,959 meetings (seed 7); for 100 tokens 20 halts, 68,251 right-end visits, 3,041 meetings.
  For long words: about 0.4 meetings per right-end visit, as in the run, one meeting in a hundred halts, so a
  right-end visit halts with probability about 0.4%.
* Nothing found in the run from blank tape makes its words special: the token statistics behind the block are those
  of fair coin flips. At the rates of random words a halt becomes likely after about 250 right-end visits, that is
  around visit 2^150 or later. The model cannot skip visits (the cascades are chaotic), and the word grows by one
  token a visit, so the tape itself would have about 2^150 tokens by then: this is out of reach.

This is an estimate, not a result: the events of one deterministic run are not independent trials, and the rate of
right-end visits is read off 31 events.

## Third look: the tape is a word over two tokens, a visit is a recursion on it

*(Superseded by the fourth look: rule (4) is decoded there, and the conjecture at the end of this section is false.)*

Cut the tape into tokens of three cells, `b = 110` and `c = 111`. Call a *visit* the moment the head stands in B on
the blank cell left of the tape. **At every visit the whole tape is a word over b and c**: all 74,198 visits of the
first 2·10^10 steps (`c/wcheck.c`; the longest word has 83,005 tokens). The periodic block is `a = c b b`
(`111 110 110`), the runs of 1s of length divisible by 3 are runs of c.

Each visit turns the word w into a word F(w), one token longer unless the visit reaches the right end. For
w = b X the next word is b V(X), with

    (1) V(b X)           = c c X                  the visit ends at the first b it is handed
    (2) V(c c b c^n b Y) = c b c c b^n V(Y)       these two pass the visit on to the rest of the word
    (3) V(c b c^n b Y)   = c b b b^n V(Y)
    (4) V(c c c ...)     : not decoded

Rules (1) to (3) give the next word at 2,239 of the 2,361 visits between the 8th and 3·10^7 steps and never a
wrong one (`py/words.py run 3e7`); at the other 122 the rest of the word starts with `c^m`, m = 3, 4, 6, 8, 10,
11 or 12. Those are the long visits that rewrite the word deep inside ("the middle eats the block") or run to the
right end and make the word several tokens longer.

What the rules say: `a = c b b` is rule (3) with n = 0, so the periodic block passes every visit on unchanged, and
the word behind it lives through a cycle of three visits, `b b b b b Y -> c c b b b b Y -> c b c c c c b Y ->
c b b  b b b b  V(Y)`: one more copy of `a`, one b fewer, and **one visit for the rest Y**. So the rest of the word
is the same system running three times slower, and so on inwards: nested counters, as in the twins
`1RB1LF_1LC1RB_...` of this group. The block collapses when the b's between two levels run out and a level meets
a `c c c`.

**The halt.** F is entered only from B reading 1, B only from A reading 0 (then the cell on its left is a 1 just
written) or from D reading 0. So the machine halts exactly when **C reads a 1 and the three cells to its left
are `0 1 0`**. In 2·10^10 steps the machine was one cell from this 12,171 times (C reads 1, D reads 0, B reads 1),
each time with a 1 in place of the first 0.

**A conjecture that would have decided it (false, see above).** For every word w over b and c, the visit on w (blank tape on both sides) leads
to a visit on a word over b and c again. Checked for all 32,766 words of at most 14 tokens and for the words
starting with b up to 16 tokens, 81,918 words in all (`py/words.py all 16`): never a halt, never another token. The word grows by up to
164 tokens when the visit reaches the right end. It fails first at 19 tokens.

**Attempts at a proof.** Finite automata reduction (`py/far.py`, `py/wfar2.py`) with, on the right side, an
automaton that remembers the nearest 6 to 15 cells and that everything beyond is a word over b, c in a known
phase: no proof; the same with windows on the left (up to 12 cells and the distance mod 3) and with run-length
windows. Reason, as far as understood: in the middle of a visit the part of the word behind the head has already
been rewritten by the inner levels, and what the head does on its way back depends on that; a window does not see it.

## Second look: when the block collapses

Following the copies of `1^5 0 1^2 0` at the left end at every visit of the left end in state D (up to 10^9 steps):
the block grows by exactly one copy every three visits and then is swallowed at once. The block had, just before
each collapse, 11, 9, 84, 36, 135, 100, 36, 324, 36, 36, 260, 999 and 36 copies (steps 29,371 to 419,367,273). The
value **36 recurs five times**, so the collapses are not random: the middle region probably triggers a collapse when
a carry inside it arrives, and the block size at that moment is set by the region's own clock. After a collapse the
left end shows `(1^8 0)^k` for a while (another word of 9 cells) before `1^5 0 1^2 0` takes over again.

## Next steps

* In Lean the model is proved sound (`lean/Sim.lean`); not proved: that `mstep` is never stuck on the states of a
  run (it never is in the computations), and that the fast program `c/wrun.c` is the same function.
* A proof of non-halting would need an invariant of the frames at the right-end events of this run, and the data
  give no hint of one; a proof of halting needs the run itself, about 2^150 visits by the estimate above. A faster
  exact method would have to skip whole cascades. The fifth look says what that is up against: the word has no short
  description by runs, repetitions or LZMA (so hashing repeated sub-words, as Hashlife does, has little to share),
  and it is rewritten whole at every right-end visit.
* What the fifth look leaves to try: the run between two collapses on the common part is one fixed sequence of
  words, `T^t(c^4 (b c c)^92 ... U^n)`, and the deep visits come at fixed t. A description of that sequence (which
  t, how deep) would predict the right-end visits of every later stretch without running it; the cascade at the
  right end would still need the word.
* The twin `1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC` (the same table started in another state, mirrored) should
  fall under the same model with another first word.

## First look

Growth class **fixed/sqrt** (left: sqrt, exponent 0.539; right: fixed,
exponent 0.433). After 1,000,000,000 steps: 63,728 cells visited (37,689 left of the
start, 9,934 right), 51,851 ones.

- left, step 975,564,704: `D>0 1 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 `
- left, step 991,221,611: `D>0 1 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 0 1^2 0 1^5 `

## Deciders tried (F11, 13 November 2026)

None closes. Each reaches a halting configuration in its abstraction, which says nothing about halting.

- n-gram CPS (`tools/c/ngramcps.c`), equal widths on both sides: a halting local configuration is reached with plain up to width 20, history 1 up to width 16, history 2 up to width 15, history 3 up to width 14, LRU history up to width 5 (larger widths ran out of the 150 s or 60 million configuration budget).
- n-gram CPS with every cell tagged by its position mod p: fails for p = 2 up to width 16, p = 3 up to width 16, p = 4 up to width 16, p = 6 up to width 16.
- n-gram CPS where each side also carries the state of a small automaton that has read that side from the far end (every automaton with up to 3 states on both sides, or 4 states on one side), with position mod 1..4 and widths 4, 6, 8: no closed set without a halt in all 120 parameter sets.
- Run-length windows (the K nearest runs of equal macro cells on each side, run lengths kept exactly below T and mod M above): fails for all 72 parameter sets (cells of 1 to 4 bits, K = 2, 4, 6, T = 2, 4, M = 1, 2, 4).
- Two-automaton closed tape language by SAT (a deterministic automaton reading each side inward, n states each, CaDiCaL): no solution for n = 2..8; n = 9 not finished in 150 s.

## Where a halt can come from

`lean/Route.lean` (kernel, written by `py/route.py`): `halt_route`, two steps before any halt the machine is in one
of: D with 0 two left, 1 left, 0 under the head.

## Pages

- [`pages/holdouts/1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA/explainer.html`](../../pages/holdouts/1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA/explainer.html)
- [`pages/holdouts/1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA/proof-status.html`](../../pages/holdouts/1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA/lean/check.sh
cd holdouts/1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA
gcc -O2 -o /tmp/wrun c/wrun.c && gcc -O2 -o /tmp/dvis c/dvis.c
/tmp/wrun word bcccbbbbccbbbbbbcbc                          # the model: HALT at step 6323
python3 py/model.py word bcccbbbbccbbbbbbcbc                # the same, every transition printed
python3 py/model.py all 17                                  # model against the machine, all words up to 16 tokens (10 s)
python3 py/model.py rec 20000                               # the two-line recursion against the model
/tmp/dvis 2e10 > /tmp/d.txt                                 # direct run, a line per visit (90 s)
/tmp/wrun dump 74198 | cmp - /tmp/d.txt && echo identical   # the model gives the same words at the same steps
/tmp/wrun enum 19                                           # the two halting words of 19 tokens (enum 1 .. 18: none)
/tmp/wrun mc 7 20000 1000 300                               # random words: 35 of 20,000 halt
/tmp/wrun mc 11 3000 10000 1000                             # longer random words: 5 of 3,000 halt (15 minutes)
/tmp/wrun run 1048576 131072                                # the run from blank tape (5 minutes; 2097152: 16 minutes)
python3 py/trec.py rec 20000 && python3 py/trec.py counter 100000   # fifth look: one recursion for T; the binary counter (1 minute)
python3 py/entropy.py /tmp/wrun                             # fifth look: the table of the words' sizes (1 minute)
python3 py/entropy.py /tmp/wrun rewrite                     # a right-end visit rewrites the whole word (1 minute)
/tmp/wrun costs 400000 3000000                              # the heavy visits (40 s); the same distances after visits 32,777 and 232,177
python3 py/entropy.py /tmp/wrun prefix 32778 232178         # the two words after the collapses share 23,257 tokens
python3 py/model_lean.py | diff - lean/Model.lean           # the generated Lean file is current
gcc -O2 -o /tmp/wcheck c/wcheck.c && /tmp/wcheck 2e10     # every visit shows a word over 110, 111 (2 minutes)
cd py && python3 words.py run 3e7                           # rules (1)-(3) against the run
python3 words.py all 16                                     # all short words lead to words (10 minutes)
python3 wfar2.py 1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA R 9 tokfar 4e6    # one of the FAR attempts
```

<!-- related machines: written by holdouts/related.py -->

## Related machines

Other holdouts of the list of 608 that are tied to this one. The comparison of tables is exact; everything about runs was checked on the first 10^7 steps of each machine and is an observation, not a proof (`holdouts/related.py`, `holdouts/related.json`).

**Same table as the machine below, started in another state.** Renaming the states as shown turns this machine's table into the other one, the halting transition included. The other machine starts in its own state A, which is not this machine's A: its run from blank tape is the run of this table started in another state. These are different runs: in the first 10^7 steps of each, no configuration of this machine's run occurs in the other, even up to a shift of the tape. So each of these holdouts is its own halting question, and settling one does not settle another.

- [`1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC`](../1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC/README.md): rename A→C, B→A, C→B, D→D, E→E, F→F and exchange left and right; it is this table started in state B, in a mirror

<!-- end of related machines -->
