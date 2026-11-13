# 1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC

bbchallenge id 113170. Halting from blank tape is open. The run is a marker whose position doubles inside a block of pairs; the whole run is the orbit of an explicit map on short lists of block sizes (fitted and checked against the machine, not yet proved), and it halts iff that orbit meets a list `[k, k]`: Collatz-like.

| state | read 0 | read 1 |
|---|---|---|
| A | 1RB | 1LE |
| B | 1LC | 0RA |
| C | 0RF | 0LD |
| D | 1LE | 1LA |
| E | 1RC | 0LB |
| F | --- | 1RC |

## What it does

Write `a = 10` and `b = 110`. At the moments the head, in B, extends the tape to the left, the tape is one block of
pairs cut by markers `b`:

    P[k0, k1, ..., kn] = B> 0 0 a^k0 b a^k1 b ... b a^kn 1          (blank on both sides)

Blank tape reaches `P[1, 1, 1]` at step 72 (Lean). From there on the run is the orbit of an explicit map on these
lists (fitted and checked, **not proved**; `py/map.py`). The run only meets two blocks `[k, m]` and three blocks
`[k, m, n]` with n odd:

| list | condition | next |
|---|---|---|
| `[k, m]` | m ≥ k+2 | `[2k+3, m−k−2]` (the marker doubles its distance from the left end) |
| | m = k+1 | `[1, 2k+3, 1]` |
| | m = k | `[2k+3]`, a block with no marker, **which halts** |
| | m < k, k−m odd | `[k−m, 2m+3]` |
| | m < k, k−m even | `[1, k−m−1, 2m+3]` |
| `[k, m, n]`, n odd | m ≥ k+2 | `[2k+3, m−k−2, n]` |
| | m ≤ k | `[1, 2k+n+4]` |
| | m = k+1 | `[1, 4k+n+10]` |

Example (steps 195 to 3,647): [1,7] → [5,4] → [1,11] → [5,8] → [13,1] → [1,11,5] → [5,8,5] → [13,1,5] → [1,35].

The first block k doubles (k → 2k+3: 1, 5, 13, 29, 61, ...) and eats k+2 pairs of the second block each time. When
the second block is too short for the next doubling (m < k+2) the marker runs off: what is left over, k−m, becomes
the new first block (if odd) or a second marker (if even), and the tail is rebuilt as 2m+3 pairs. With two markers
(n odd) the same overflow wipes everything into one block of 2k+n+5 pairs with a fresh marker.

**Halting.** A block with no marker, `P[N] = B> 0 0 a^N 1`, halts after 2N+7 steps, for every N (Lean,
`single_halts`): F and C walk right over the pairs and F reads the blank cell after the tape. In the map this
happens exactly from `[k, k]`: the second block is exactly as long as the first. So, by the fitted map:

    the machine halts from blank tape  iff  the orbit of [1, 1, 1] meets a two-block list [k, k].

In the orbit k is always odd, and m changes parity at every doubling, so parity does not exclude m = k; neither does
any residue of k − m modulo 3, 4, 5, 7, 8, 9, 12, 16, 24, 32 or 48 (each residue 0 occurs at the expected rate in
3·10^6 iterations). The blocks grow exponentially (about 900 bits after 2.4·10^8 iterations), so a hit becomes ever
less likely: this is a Collatz-like question, a "cryptid" in the bbchallenge sense, as the community tracker says.

## What is proved (Lean, kernel; `lean/check.sh` prints ALL CHECKED)

- `lean/Halt.lean`: `blank_to_P` (blank tape reaches `P[1, 1, 1]` in 72 steps) and `single_halts` (`P[N]` halts for
  every N).
- `lean/Rules.lean` (from `py/rules.py`): the sweeps `d_run`, `a_run`, `b_run`, `a_left`.
- `lean/Blank.lean` (generated): the halting configurations, no halt in 10^4 / 10^7 steps.

## Checked, not proved

- `py/map.py table`: the formulas against a direct run of the machine from `P[k, m]` and `P[k, m, n]`, k < 9,
  m < 13, n < 8 (1,053 lists, including n even, where the formulas are different and are in `py/map.py`); `P[N]`
  halts for N < 40.
- `py/map.py check 4e7`: from blank tape the machine follows the map at all 214 marker configurations up to step
  36,965,083 (`[1021, 819]`).
- `py/map.py far 3e8`: no list `[k, k]` in 3·10^8 iterations of the map from `[1, 1, 1]` (exact integers, about 3 minutes); the blocks
  are then numbers of about 1,000 bits.

## Open

- Halting: whether the orbit of `[1, 1, 1]` ever meets `[k, k]`.
- The map itself is not a theorem. A proof needs the doubling pass as an induction (each pass is k+1 rounds of a
  zig-zag; the rounds are visible as `a^j B> 0 0 a^i b a^m ...` with (j, i, m) → (j−1, i+2, m−1)) and the five
  overflow cases; `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA/lean` (same k → 2k+3 doubling) is the model to follow.
  With that, `halts iff the orbit of [1,1,1] meets [k,k]` becomes a Lean theorem.

## Reproduce

```sh
. /etc/profile.d/lean.sh && holdouts/1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC/lean/check.sh
python3 holdouts/1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC/py/map.py table
python3 holdouts/1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC/py/map.py check 4e7
python3 holdouts/1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC/py/map.py far 3e8
./tokrun 1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC 1000000000 a=10,b=110 L     # the tape at left extensions
python3 holdouts/1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC/py/rules.py > lean/Rules.lean
```

## Pages

- [`pages/holdouts/1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC/explainer.html`](../../pages/holdouts/1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC/explainer.html)
- [`pages/holdouts/1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC/proof-status.html`](../../pages/holdouts/1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC/proof-status.html)
