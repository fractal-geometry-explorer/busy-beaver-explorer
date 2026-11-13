# 1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA

bbchallenge id 82928. One of the six-state holdouts whose halting from blank tape is open (group G11, family **two-ended counter, (10)^n left / 110 digits right**). The pages are built from [`status.json`](status.json).

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | --- |
| B | 1LC | 1RF |
| C | 0LE | 0RD |
| D | 0RB | 0LC |
| E | 1RD | 0LD |
| F | 0RC | 0RA |

## Status

Open. Lean (kernel): the halting configurations and bounded runs (`lean/Blank.lean`), the halt from `B> 1 1 1` (`halt_ctx`; that every halt passes through it is from the table)
and shift rules (`lean/Rules.lean`), 128 event rules for all sizes (`lean/Events.lean`). C: no halt in 3·10^10 steps.

## What it does

An **event** is the head in state D on cell 110 (cells counted from the start cell; the busiest place from step ~10^8
to 3·10^9: 18,547,861 visits in steps 10^9-2·10^9, `c/busy.c`). Around it the tape is

    ... [high] (1000 110)^p [middle] [boundary] [low] D> [phase] [R] ...

- `low`: binary, 4-cell digits `0100`/`0101` (two-event epochs) or `0001`/`0101` (one-event epochs), lowest digit
  next to the head, 0 to 3 digits;
- `middle`: binary, 11-cell digits `1000 1000 110` = 0, `1010 1000 110` = 1; boundary `1000 11` or `1000 110 1`;
- spacers `1000 110` (p of them), crossed by the carry and never changed;
- `high`: binary, 4-cell digits `1000`/`1010`, with many leading zeros;
- `R`: binary, 3-cell digits `100`/`000` after the phase `0001 0000`/`0101 0000` (or `001`/`000` after `0001`),
  lowest digit first.

low + middle + high is one binary number. In a two-event epoch the events alternate: one adds 1 to the left number
(phase `0001 0000` -> `0101 0000`, 12n+4 steps for n carried ones), the next adds 1 to R (8k+24 steps). In a one-event
epoch each event adds 1 to both. So both sides count the same events. Example (steps 200,000,018-200,000,282, events
4,978,485-4,978,497): low goes 1, 2, 3, 4 = wrap (middle +1), ..., R goes 2, 3, ..., 8.

**Epochs.** When the high counter overflows the head visits the left end (steps 849,584, 1,310,756, 4,549,244,
14,464,476, 29,592,096, 90,908,434, 213,566,522, 359,041,718, 657,870,796, 1,057,368,168, 1,834,353,438,
3,023,431,124; two new cells each time) and rewrites the left part; each visit moves the low/middle boundary one digit
(low has 3 digits from 9.1·10^7, 2 from 2.1·10^8, ..., 1 from 1.06·10^9, 0 from 1.83·10^9) and switches between the
two kinds of epoch. The sweeps also write junk words (`1010101010`, ...) into R, which then has a low segment, junk
and higher segments. After step ~3.02·10^9 the engine moves to cell 111 (82,815,736 visits of D on cell 111 in steps
2.5·10^10-3·10^10): the same counters in a shifted alignment (one low digit; R's low segment 4 digits), not decoded.

**Proved (lean/Events.lean, 128 theorems, kernel).** Seven counter rules for every size (`t_inc_low`, `t_inc_R`,
`t_inc_both`, `t_carry_alt`, `t_carry_both`, `t_carryH_alt`, `t_carryH_both`: carries over n low ones, j middle ones,
p spacers, i high ones, k ones of R), and 121 rarer events mined from the run (`py/miner.py`).

**Coverage** (`c/evcov.c` with `c/rules.txt`, first 3·10^9 steps): 45,121,817 events; the seven counter rules match
44,107,018 (97.8%), all 128 rules all but 256,981 (99.43%). 256,975 of these are one shape: R's 6-digit low segment
wrapping into the junk after it (once per 64 R increments in the epoch from 1.83·10^9); the rest are first events
after left-end visits.

**Where it can halt.** From `B> 1 1 1` it halts (Lean `halt_ctx`); every halt passes through it (from the table). In 3·10^9 steps B has `1 1` ahead 201 times: 50 before
the first event, 126 inside proved rules (followed by 0: the rule runs on), and 25 in uncovered events: the sweeps
after the left-end visits at steps 90,907,918 and 359,041,190 (B every 7-15 cells from cell 21 to 100, through the
high counter) and four wraps of R (cells 149-199, at the right end of R). It follows (from the rules and the table, not as a theorem) that halting is a question about the
words these sweeps and wraps meet.

## Files

- `py/events.py` writes `lean/Events.lean` (`python3 py/events.py lean > lean/Events.lean`) and the coverage rules
  (`python3 py/events.py cov > c/rules.txt`); the mined rules are in `py/mined.txt`.
- `py/autoev.py`, `py/miner.py` (shared by the batch-5 folders of G11): prove the rule from an event pattern by
  running `bbtools.symtm` until the head is back on the event cell; mine rules from unmatched events
  (`python3 py/miner.py M D WORDS PAIRS 400`, WORDS e.g. `10101000110,10001000110,1000110,0101,0100,1010,1000,0001,100,001`).
- `c/evcov.c` (shared): `gcc -O2 -o evcov c/evcov.c -lm && ./evcov M 3000000000 110 D c/rules.txt 0 0 B:11` prints the
  hits per rule, the unmatched count and every `B> 1 1` with the rule of its event (`MISS` = uncovered); with K > 0
  it prints the first K unmatched events each with the next event (input of `miner.py`).
- `c/busy.c` (visit counts per cell and state), `c/ev.c` (the tape at each event); `c/forbid.c`, `c/ctxcount.c`,
  `py/residue_blocks.py` as before; `lean/rules.py` writes `lean/Rules.lean`.

## Next steps

Write R's junk words and higher segments as counters (the wrap into the junk as one rule with the junk as a
parameter) and the left-end sweep as a rule on the high counter; decode the layout with the engine on cell 111.

## Pages

- [`pages/holdouts/1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/explainer.html`](../../pages/holdouts/1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/explainer.html)
- [`pages/holdouts/1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/proof-status.html`](../../pages/holdouts/1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh
holdouts/1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/lean/check.sh
gcc -O2 -o tmrun tools/c/tmrun.c && ./tmrun 1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA 100000000000
gcc -O2 -o ctxcount holdouts/1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA/c/ctxcount.c && ./ctxcount 1RB---_1LC1RF_0LE0RD_0RB0LC_1RD0LD_0RC0RA 1e10 B 3
```
