# 1RB0LA_1RC1RA_1RD1RE_1LC---_0RB1LF_1RA0LE

bbchallenge id 124869. One of the six-state holdouts whose halting from blank tape is open (group G11, family **blocks of 4m+2 ones, irregular digits**). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 0LA |
| B | 1RC | 1RA |
| C | 1RD | 1RE |
| D | 1LC | --- |
| E | 0RB | 1LF |
| F | 1RA | 0LE |

## Status

Open. Lean: the halting configurations and bounded runs (`lean/Blank.lean`); the halting context `C> 0 1`, four contexts that lead to it and 7 shift rules (`lean/Rules.lean`, kernel); the converse, every configuration that halts 1, 2 or 3 steps later (`lean/HaltPred.lean`, kernel). C: no halt in 20,000,000,000 steps; the gap-parity law (below) holds in 3·10^9 steps.

## What it does

The head sweeps back and forth and rewrites the tape on every pass. Moving left, E and F alternate on a block of
1s (E keeps a 1, F writes a 0), so `1 1 1 1 1` becomes `1 0 1 0 1`; A, entered from F on a 0, erases a run of 1s.
Moving right, A writes a 1 on each 0 and B steps over each 1, so an alternation becomes a solid block again; at a
run of 0s, A, B, C and D fill up to four cells and D turns back. Between sweeps the tape left of the head is a list
of blocks `0 1^a` with a even (mostly 2 mod 4, sometimes 0 mod 4) and the tape right of it a list of alternations
`1 (0 1)^k` separated by gaps `0^(4j+2)`; the two ends of the tape are irregular (`c/at.c` samples it).

Halting: the halting transition is D reading a 1, reached only from `C> 0 1` (both directions in Lean: `halt_ctx`, `halt_iff_1`). Going back further (Lean,
`lean/Rules.lean`): moving right, B on `0 0 1` or A on `0 0 0 1` halts, and so do `0 B> 1 1 1` and `0 F> 0 1 1`
(A erases the two 1s and turns onto `0 0 1` in B). The only other configuration two steps before a halt is `0 D> 0`
(`halt_pred_2`), which cannot occur since D is entered only from C writing a 1 and moving right (from the table, not
in Lean).

**The gap-parity law.** Each time the head moves right from a 1 onto a 0 (`c/gaps.c`, 3·10^9 steps): A finds a
single 0 (290,346,873 times) or a run of even length (2 mod 4: 96,765,873; 0 mod 4: 1,283), never an odd run; B
finds a single 0 (48,384,348) or an odd run (1 mod 4: 96,764,414; 3 mod 4: 1,632), never an even one. The halt needs
exactly the missing cases (a run of 3 before A, of 2 before B). So the machine halts if and only if, eventually, a
right sweep reaches a gap with the wrong parity for its arrival state. Why the parity holds is not proved: A and B
alternate cell by cell on an alternation, a trip with A arriving fills 4 cells of a gap and one with B arriving 3,
and the left sweeps leave gaps of length 2 mod 4, but the bookkeeping through the irregular ends was not done.

Automata tried (none closes):
- `c/far.c` (finite automata reduction: a DFA of n states on the left part, the least co-closed NFA on
  (state × DFA state) + bottom for the rest): no certificate with n ≤ 7, DFA on the left or on the right (23,836,540 DFAs each way at n = 7).
- A closed-tape-language search whose automata on each side are a hand-written grammar (blocks `1^(4m+2)` on the left,
  alternations and gaps `0^(4j+2)` on the right, lengths mod 4) times a window of 2–8 cells, started from blank tape
  or from the configuration at step 1,000,002: the abstract run escapes the grammar at the two ends of the tape
  (the left blocks of length 0 mod 4, the right end's lone 1 and free gap) and reaches a halt.

## Files

- `lean/HaltPred.lean` (every configuration that halts after exactly k more steps, k = 1, 2, 3, both directions) is written by
  the batch's generator: `python3 ../1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB/py/halt_pred.py 1RB0LA_1RC1RA_1RD1RE_1LC---_0RB1LF_1RA0LE 1 2 3 > lean/HaltPred.lean`.
- `lean/rules.py` writes `lean/Rules.lean` (the halting contexts and the shift rules, proved by `bbtools.symtm`):
  `cd lean && python3 rules.py > Rules.lean`.
- `c/gaps.c`: the gap-parity counts, `./gaps M 3000000000` (about 30 s).
- `c/at.c`: the tape each time the head is in a state on a symbol, `./at M 300000000 E 0 1000`.
- `c/far.c`: the finite-automata-reduction search, `./far M 7` and `./far M 7 m` (shared by the batch).
- The near-miss counts come from `c/ctxcount.c` and `c/forbid.c` in
  [`../1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c`](../1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c).

## Next steps

Prove the gap-parity law: write the round trip of the head as a rule on (left block, gap, arrival state) and show the
parity is kept, then encode it as a closed language for `TM/CTL.lean` whose right automaton counts gap lengths mod 4
together with the parity of the position since the start of the current alternation, and which treats the two ends
of the tape by their own small grammars (the right end: a lone 1 and a gap, both changing at each visit).

## Pages

- [`pages/holdouts/1RB0LA_1RC1RA_1RD1RE_1LC---_0RB1LF_1RA0LE/explainer.html`](../../pages/holdouts/1RB0LA_1RC1RA_1RD1RE_1LC---_0RB1LF_1RA0LE/explainer.html)
- [`pages/holdouts/1RB0LA_1RC1RA_1RD1RE_1LC---_0RB1LF_1RA0LE/proof-status.html`](../../pages/holdouts/1RB0LA_1RC1RA_1RD1RE_1LC---_0RB1LF_1RA0LE/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB0LA_1RC1RA_1RD1RE_1LC---_0RB1LF_1RA0LE/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB0LA_1RC1RA_1RD1RE_1LC---_0RB1LF_1RA0LE 20000000000
gcc -O2 -o ctxcount holdouts/1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c/ctxcount.c && ./ctxcount 1RB0LA_1RC1RA_1RD1RE_1LC---_0RB1LF_1RA0LE 1e9 C 2
```
