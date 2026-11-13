# 1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD---

bbchallenge id 16609. One of the six-state holdouts whose halting from blank tape is open (group G07).
Family: **binary-ruler counter list** (a list of counters drained at rates 1/2, 1/4, 1/8, ... while the last one
fills, rebuilt whenever the carry runs off the list). Decision: **open**.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1RC |
| B | 1LC | 1LE |
| C | 1RD | 0RA |
| D | 1LB | 0RA |
| E | 0LD | 1LF |
| F | 1LD | --- |

## What it does

Look at the tape each time the head is in state A on the blank cell just right of the tape (`A> 0^inf`, a *visit*).
The tape is then a list of counters

    0^inf  (10)^c0 s0 (10)^c1 s1 ... s(m-2) (10)^c(m-1)  A>

with single separator cells `s_i` in {0, 1}. A counter can be 0 (a *zero slot*); in the run it only appears between
two separators 0 (the tape shows `00`, or `000` for two slots), or at the front as the *prefix* (c0 = 0, s0 = 1: the
tape starts with a lone 1). `py/counters.py` has the complete rule; in words:

**The carry.** It starts at the last counter i = m−1:

* s(i−1) = 1: the separator becomes 0, and the target is c(i) if c(i) is even, c(i−1) if c(i) is odd;
* s(i−1) = 0 and c(i) even: the target is c(i−1);
* s(i−1) = 0 and c(i) odd: the carry moves on to i − 1.

An *ordinary* visit: the target is ≥ 1, it loses 1, and the last counter gains 3. Every decrement flips a parity, so
the parities are a binary counter: c(m−2) loses 1 every second visit, c(m−3) every fourth, and so on, while the last
counter grows by 3 a visit, e.g. (5, 9, 18, 2) → (5, 9, 17, 5) → (5, 8, 17, 8) → (5, 8, 16, 11) → (5, 7, 16, 14).

**Rebuilds** (the rare events; 71 of the first 10^8 visits):

* *front*: the carry passes the first counter. If c0 is even, the tail is rebuilt from c0; if odd, a new counter 0
  is put in front with separator 1 and the tail is rebuilt from it (so the list starts with a new counter 1).
* *slot*: the target is a zero slot and the counter x left of it is ≥ 1: x loses 1, the slot disappears, x and the
  counter y after it are joined by a separator 1, and the tail is rebuilt from y.
* *merge*: the target is a slot and x is a slot too: the counters left of x and right of the target are added
  together, both slots disappear, and the tail is rebuilt from the sum.
* *prefix*: the target is the prefix (reached from an odd c1): the prefix disappears and the tail is rebuilt from
  c1, which gains one more.

*Rebuild the tail from y*: every separator from y to the end becomes 1, y gains 1, the last counter gains 1, and a new
last counter 2 is appended after a separator 0. Normal form: a zero counter between a separator 1 and a separator 0
is the same tape as its neighbours merged plus one ((10)^a 1 0 (10)^b = (10)^(a+b+1)), the "43 1 1 1 167 → 211"
merges of the earlier pass.

**Steps.** With S the sum of the counters from i (where the carry stopped) to the end, n = m − i and u the number of
separators 1 from s(i−1) on: ordinary visits take 6S + 6n + 12 steps (s(i−1) = 0), 6S + 6n + 5u + 5 (s(i−1) = 1,
c(i) odd) or 6S + 6n + 4u + 4 (c(i) even); a front or slot rebuild 6S + 28 (S over the counters from the slot or
the front); a prefix rebuild 6S + 10u + 20.

**The long run.** Each rebuild at the front adds a counter, merges remove some; the first counters drain ever more
slowly, because only a carry that runs through the whole list reaches them (about once in 2^(m−1) visits), and when
the first counter runs out the next one takes its place:

    visit 446,127      step 5.4·10^11   m=17  first counters 13 148 343 139
    visit 15,604,278   step 7.1·10^14   m=21  117 281 13 2071   (the first two had run out)
    visit 100,000,000  step 2.4·10^16   m=25  102 2287 7632 12823 32143 ...

## Where it can halt

Only F reading 1. On the random lists of the shapes the rule covers (all five kinds of visit), the machine never
halts within the visit. Leaving those shapes needs a zero slot next to a separator 1 (`01` or `11` on the tape), which
the rule never produces except when a slot rebuild finds a counter x = 1 left of the slot (x − 1 = 0 is then followed
by the new separator 1). Even then a halt is not forced: of 400 random lists with that event (`x = 1`, random
counters around it) the machine halted within 300 visits in only 8 (2%), the others went back to the rule's shapes.
A closed tape language from windows of 6 cells (`python3 -m bbtools.ctl MACHINE 6`) further confines the halting
step to the left end of the tape.

### The accelerated run (fourth pass)

Between two rebuilds the order of the visits depends only on the parities and the separators: once its separator
is 0, position k (counted from the front, m counters) is examined by the carry every 2^(m−1−k) visits, and it stops
the carry and passes it on in turn. `py/accel.py` computes these schedules as eventually arithmetic sets of times
(from the right end inward, O(m) work), finds the next event (the carry passing the front counter, a counter reaching
0, a zero counter being targeted) in closed form, does that one visit with `counters.step`, and repeats. It agrees with
`counters.step` run visit by visit at 31 sample visits up to 10^6 (and at 31 up to 3·10^6). It runs

* **10^1757 visits** (m = 5,837 counters; 39,517 events, 15,505 slot or merge rebuilds) in 45 minutes, always inside
  the rule's shapes; every visit costs at least one step, so this is **no halt in 10^1757 steps** (the step count
  itself is not tracked; it is far larger).
* The smallest counter left of an emptied counter (not the first counter) is still the early 6 (visit ~2^10). Later
  the small ones come from the front, whose counters stay in the thousands: x = 2,984 at visit ~2^577, 17,741 at
  ~2^643, 1,186 at ~2^1158. The sum of 1/x over the slot rebuilds is 0.227, of which 0.0013 after visit 2^30 and
  2·10^−5 after 2^2000: if x were a random number of its size, the chance of an x = 1 still to come is below 10^−3,
  and an x = 1 halts the machine only now and then (above).

## Status

* **Lean (kernel)**: `lean/Rules.lean`, generated by `py/rules.py`: the visit-to-visit rule for the last two counters
  in all eight parity cases, for every value of the counters and every tape to their left.
* **Lean (kernel)**: `lean/Macro.lean` with the pieces of `lean/MacroRules.lean` (generated by `py/macro.py`):
  theorem `ordinary_visit`: for **every** counter list on which the rule `ordinary` is defined (every visit that is not
  a rebuild: the carry stops before the front counter and does not target a zero counter), the machine goes from its
  tape to the tape of the result. The leftward pass (`start`, `cross`, `turn`, `turnA`) turns the crossed counters
  into blocks of 1s; the way back (`ret`, `endr`, by induction in `retB`) rebuilds them, the last counter with 3 more.
  `py/macro.py check 20000`: the Python mirror of `ordinary` agrees with the machine on 14,249 random lists and with
  `counters.py` at the 19,972 ordinary visits among the first 20,000 from blank tape (`none` exactly at the rebuilds).
* **Lean**: `lean/Blank.lean`: the halting configurations; no halt in 10^4 steps (kernel), 10^7 (`native_decide`).
* **Trusted**: `py/counters.py`: the complete rule with the step count of every visit. It agrees with the machine on
  6,000 random lists (ordinary visits, all four kinds of rebuild, slots and the prefix; the step count too), and with
  every one of the first 37,148 visits from blank tape (3·10^9 steps, printed by `c/tokvisits.c`), counters and step
  counts both.
* **Trusted**: `py/longrun.py`: the rule run from the first visit: **no halt in 10^8 visits (2.4·10^16 steps)**,
  never leaving the shapes the rule covers. (The earlier exact simulator `py/blocksim.py` reached 5.4·10^11 steps;
  at its last visit, 446,127, the two agree.)
* **Trusted**: `py/accel.py`: the rule run exactly with the odometer in closed form: **no halt in 10^1757 visits**.
* **Trusted**: the CTL confinement (windows of 6) to the left end.
* **Heuristic**: a halt needs a slot rebuild with x = 1 (and then only sometimes halts); the x values met are large
  and the sum of 1/x after the first 2^30 visits is 0.0013.
* **Open**: whether a slot rebuild ever meets a counter 1 on its left (or the run otherwise leaves the rule's shapes).

## Next steps

* The rebuilds in Lean. They are not local on the tape: a carry that meets an emptied counter through F writes a 1
  there and keeps scanning left (D), possibly to the front, and the way back then runs in a second phase (C reads
  even blocks, every separator becomes 1, a counter 2 is appended at the end:
  `L 1 0 1 C> 1^(2c) 0 1 1 R` → `... C> R`, `L 1 0 1 C> 1^(2c) 0^inf` → the visit). B meeting an emptied counter, or
  the blank at the front, starts that phase at once (`L 0 B> 0 1 R` → `L 1 0 1 C> R`, 4 steps). With these pieces and
  a phase flag in `scan`, the whole rule and a `nonhalt_of_orbit` as for 1RB1RA_0LC1RF_0LD1LD_1LE1LC_0RB0RA_---1RE
  follow the same pattern as `ordinary_visit`.
* Then the question is about the counter list only: show that a counter next to a draining slot is never 1 when the
  carry reaches the slot. Between rebuilds `accel.py`'s schedules are exact formulas; what decides x is the value the
  neighbours had at the last rebuild, which comes from the growth of the last counter (3 a visit) between rebuilds, so
  any invariant has to control those exact values. This looks as hard for this machine as for the others in the
  group whose halting is a coincidence of large numbers.

## Pages

- [`pages/holdouts/1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD---/explainer.html`](../../pages/holdouts/1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD---/explainer.html)
- [`pages/holdouts/1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD---/proof-status.html`](../../pages/holdouts/1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD---/proof-status.html)

## Check

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD---/lean/check.sh
cd holdouts/1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD---/py
python3 counters.py random 6000                                # the rule against the machine, random lists
gcc -O2 -o tokvisits ../c/tokvisits.c && ./tokvisits 3000000000 > visits.txt && python3 counters.py visits visits.txt
python3 longrun.py 1e8                                         # 10^8 visits, ~4 minutes
python3 accel.py check 1e6 && python3 accel.py far 1757 2700   # the odometer in closed form, 10^1757 visits
python3 macro.py check 20000 && python3 macro.py > ../lean/MacroRules.lean   # the Lean rule; regenerate the pieces
python3 rules.py > ../lean/Rules.lean                          # regenerate the Lean rules
gcc -O2 -o tmrun ../../../tools/c/tmrun.c && TMRUN=./tmrun python3 bscheck.py 1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD--- 10 A R 20000000
cd ../../../tools/py && python3 -m bbtools.ctl 1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD--- 6
```
