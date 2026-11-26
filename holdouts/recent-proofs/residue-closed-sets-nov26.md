# Closed sets of residue classes on the closed-form maps: none (26 November 2026)

Section G of `technique-survey-nov26.md` proposed to search, for the machines reduced to a closed-form map, for a
finite set of (residue mod m, phase) classes that is closed under the map and avoids the halting values. This note
records the outcome for every target named there. No closed set was found on any of them, so there was nothing to
check in Lean. Everything new here is a Python search (trusted, not proved); the result for the first three
machines was already a Lean theorem.

| machines | map | what was searched | outcome | where |
|---|---|---|---|---|
| 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE, 1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE, 1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE | n → 3n − 10·2^k + 3k + 14, halt at 5·2^k − k − 6 | nothing new: already in the repository | **no congruence of any modulus**, from any start (`no_cong_ever`, kernel); none with size cells either, up to 81 cells and residues mod 2^5 (`py/trapsize.py`) | `lean/CongAll.lean`, `py/trapsize.py` in the first machine's folder |
| 1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE, 1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE, 1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE, 1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE | s → 2s mod L, L → L + 2, fatal at the midpoint when L is on a doubling list | classes (s mod N, distance of L from the fatal L of its level mod N, level mod its period, cell of s/L, half of the level); N = 2..13, 15, 16, 24, 27, 32; 2, 8 and 32 cells | all 51 searches per machine reach a fatal midpoint class | `py/sizeresidues.py` in the first machine's folder (the plain residue search to N = 48 was there before: `py/doubling.py residues`) |
| 1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD | two counters; a chain start (x, m0) halts iff x = 2^(k+3) − k − 5 (m0 = 1) or 5·2^(k+1) − k − 6 (m0 = 3) | classes (x − h_k mod N, level mod its period, m0, cell of the level); N = 2..48, 64, 81, 96, 128, 243, 256 with 1 and 16 cells, ten small N with 64 and 256 cells | all 126 searches reach the class of a halting value, in at most 11 classes | `py/residues.py` in its folder |
| 1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA | f(10a + d) = 31a + K[d/2] | closure of the class of 22 mod M, M ≤ 2000 | every class, except that mod 31 the class records the previous r (no restriction on the next r); and the halt is not a value of the orbit | `py/residues.py` in its folder; `rlist_onto` in `lean/DigitClosed.lean` |

## How the searches work, and what a hit would have meant

A class stands for all numbers with the same residues, the same level modulo a period and the same rough size
inside the level. From every class reached, the search takes members of many sizes, applies the exact map and adds
the classes of the images. Each transition is a real step of the map, so the classes reached form a lower bound of
what any closed set holding the start must contain. If they include the class of a halting value, no closed set of
that kind exists. If the search had closed without one, the set would have been a candidate invariant, to be proved
in Lean with all branches (the sampling could miss a branch). That did not happen in any search.

Two things are worth keeping.

1. **Plain residues say little for the doubling-type maps.** The halting values c·2^k − k − d run through many
   residue classes as k varies (for 1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD, through every class mod every
   N < 200), so a class system has to carry the level k, modulo a common period of k and 2^k. The searches here
   do; the older `py/doubling.py residues` took the fatal lengths for every k at once.
2. **Adding the rough size does not help.** In the size coordinate each of these maps is expanding with full
   branches (x → 3x or (3x − 1)/2 for the first group, x → 2x mod 1 for the second, the chain of doublings for the
   third), so every cell reaches the cell of the halting value, and the residues mix on the way.

What is left for these machines is what the folders already say: a proof would have to follow the exact size and
the exact residues together, which is the Collatz-like problem itself. Section G can be closed as a negative.
