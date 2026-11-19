# Attractors group: techniques of busycoq PRs 78, 79, 80, 86, 95 (Alex Havrilla, DeepMind)

All five PRs share one skeleton: `multistep_nonhalt` (a vm_compute'd entry run from `c0`) followed by
`progress_nonhalt` on a predicate `InAttractor` closed under `-->+`. They differ in what the attractor is.

## PR 78, 1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD--- (exponential linear-form attractor)
- Attractor `attractorCfg N = rep110 N (S1 >> 0inf) {{B}}> (S0 >> 0inf)`, i.e. `0^inf 1 (011)^N B>0 0^inf`, with a ghost
  index m: `Inv m N := m >= 10, m even, N even, 600 s4(m)+200+2000m <= 9N <= 615 s4(m)+205-2000m`, s4(m) = (4^m-1)/3.
- Macro layer: chunk-RLE over 110/001 triplets (`LChunk/RChunk`, counts in binary N), six base rules, three quadratic
  "era" contractions proved by induction, and `super4x_iter`: (001)^c 0 (001)^(2c sum4 m + m + d) -> (001)^(c 4^m) 0 (001)^d.
- Entry: 1 raw step + 17,205 `stepFast` macro steps (vm_compute) to N0 (277 bits), `Inv 136 N0` by reflection.
- Cycle: 642 symbolic macro steps over `LinForm = aN*N + aQ*s4(m) + am*m + ac` (vm_compute), with sound sign/parity
  deciders under Inv (parity of a LinForm is (aQ+ac) mod 2 since N, m even and s4 m odd); result (m,N) -> (m+4, 256N+54-180m);
  `inv_step` by lia using s4(m+4) = 256 s4(m) + 85.
- Generality: needs a run that eventually locks into a regime where one fixed sequence of macro rules repeats, every
  count being affine in (N, b^m-type geometric sums, m), and a band invariant (ratio N / b^m confined) that fixes all
  signs and parities the sequence tests. Machines with "counter paid by a run, exact-hit halts" (Collatz-like coincidence
  only in appearance) where empirically the phase pattern becomes periodic are the targets. Fails if the parities truly
  wander (genuine Collatz behaviour).

## PR 79, 1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA--- (same table as 78, other start state)
- Same attractor and same 642-step lap (state C here). Four stages: 595,860 concrete macro steps (vm_compute) to
  `p60Cfg a b = 0inf C> 0 (001)^(a-1) 0 (001)^(b-1) 0inf` with a, b of 5,292 / 5,236 bits; a symbolic 60-step "highway"
  lap p60(a,b) -> p60(4(a-b), 4b) under `InvB` (b>=16, 6b<=a, a,b = 0 mod 4), iterated K = 115,895,156,973,855,250 times
  by induction (`period60_iter`: p60(a,b) -->* p60(4^K (a-Kb), 4^K b)); 2,083 symbolic steps (LinForm in s4(K), K) into
  `attractorCfg` with m = K + 2630; then the 642 lap.
- Generality: shows the attractor technique tolerates a long linear "highway" (ratio a/b decreasing by 1 per lap) as
  long as the highway itself is a symbolic lap with an inequality invariant; the number of highway laps is a concrete
  big number but never unfolded.

## PR 80, 1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA--- and 1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD--- (era invariant)
- Family `mCfg m z c k = 10110 (100100110)^m 10 A>1 (011)^(6k+7) (001)^z (011)^(3k+1) 0111 (011)^c 01` (176's frame;
  600 by `isoCfg` = mirror + A<->D). `InvM := k<=5, z>=1, m>=33, 9m<=c, 2100<=c`. Pure inequalities, no ghost index.
- Round: m = 11K + r; `era_L11_d0_loop` (K passes: -11 wLM, 18 wT moved; needs c >= 18K); then case split r in 0..10,
  z in {1, >=2} (22 cases), each a `symRunBits` run over 5-variable affine `SymN` tokens plus two more induction loops
  (`era_conv_loop`: 2 wZ -> 4 wT; `era_E_loop`: rebuild of wRM words 6 at a time) through ~15 intermediate families
  each with its own Inv*, landing in mCfg with InvM. ~255 vm_compute'd symbolic certificates; files ~9,900 lines.
- Entry: 11 (resp. 14) symbolic chunks to mCfg(152,218,2162,5) (step 42,869,330 by our simulation) resp. mirrored
  mCfg(91,1,2200,2) (step 28,268,016).
- Generality: works for "nested crossing counter"/phase machines where the repo already has the phase periods and a
  closed node set "under size assumptions": the missing piece is a family of linear inequalities preserved by every
  residue case. Needs bounded number of residue cases per round (here m mod 11 x z-cases) and a growth that keeps the
  inequalities slack (ratios between blocks confined).

## PR 95, 1RB0RE_1LC1LF_1RA0LD_1LB1LA_1RB1RC_---0LA (exact transient + translated cycler)
- Final shape `(encW 18 restL) {{A}}> (S1 >> 0inf)` = `restL (011)^18 A>1 0^inf`; `cyc_reaches`: 2,035 raw steps,
  parametric in restL (never read; head reaches 53 cells left), shift +7, writes 0011011 (checked by our simulation).
- Transient: 166,268 `stepOuter_B1` hybrid macro steps (48,586,387 clean-loop steps, 3,152,537 general transitions,
  ~7.93e889 raw steps, ~2,956-bit counts of 110 words), one `vm_cast_no_check`, with a home-made radix-64 `D64/Big`
  arithmetic (no Uint63/primitive integers) certified against a nat reference stepper.
- Generality: any machine whose run eventually becomes a translated cycler (or any finite-window recurrence) after
  a transient that an exact macro simulator can traverse. No insight into the transient needed; the cost is the length
  of the transient in macro steps. Candidates are machines whose exact accelerated runs show a regime change into
  a periodic drift; we have no cheap test for that without running an exact accelerator far.

## PR 86, 1RB0RE_1LC0RA_1RE1LD_0LB0LF_1RA1RA_0LD--- (base-4 carry engine + parametric window)
- Tokens: cells, runs of 00/11/01/10/110110, and base-4 digit blocks `tdb m val` (digit d as 6 cells: 0 011001,
  1 001001, 2 111001, 3 101001); `Absorbs`/`Carries` lemmas: a block absorbs `amt` pulses as val + amt with carry
  (`Absorbs_db`), wrap after 4^m. Engine `runStepsPos` with binary-N counts.
- Entry: 84,472 engine steps (~10^708.37 raw, ~2,350-bit counts) to window `checkWindow`: state D, top 40 left tokens
  (89 cells) fixed, right tokens [0, (110110)^1, (00)^2, (11)^1] then blank. Lap: 6,419 engine steps from the window
  return to it with a longer left tail, parametric over restL (Stream). Both by `vm_cast_no_check`.
- Raw lap length unknown: our plain simulation from the window (blank restL) has no recurrence in 2e10 steps; the
  head creeps right like a counter. So it is a translated cycler of astronomically long period, found only because
  the engine accelerates the digit counters.
- Generality: two-level / shift-overflow counters whose run after enough rebuilds settles into a self-reproducing
  window. Needs: an exact token engine for the machine's digit encoding with proved carry rules, and a run that
  actually reaches a window (not provable in advance).

## Candidates (decision "open")
- 1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC: each pass doubles the first block (k -> 2k+3) at the cost of the second,
  blocks rebuilt when it runs out, whole run an explicit map on lists of two or three blocks: the 78/79 shape (counter
  paid by a run, rebuild), so look for a regime where the map's lap becomes fixed with a band invariant.
- 1RB0LC_1LC0RE_1LD1LB_1LA1LD_1RF0RA_---1RE (G01, same group as 78/79): list (100)^x 1011 [(010)^a 11]* (010)^n 01
  over the period-3 background with a front counter; same triplet encoding as rep110/rep001, attractor technique.
- 1RB0LD_1RC0RF_0LD0LE_1RF1LC_0LB1LE_0RA--- (G01): nested counter on (010)^n blocks, i-th block loses 3*4^(i-1) per
  visit: geometric 4^i sums are exactly what LinForm with s4 handles.
- 1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC: levels 1^X a 00 a^Y, each cycle X+15, Y-1, rebuild at ~7 per word,
  growth 15/7 with remainders steering, can halt only at the right edge (Lean): PR 80's era technique (bounded
  residue cases + inequalities).
- 1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA (Quadratic Mess, same tracker class as all of PR 78-95 except 86): a few
  long blocks changing by fixed amounts per round trip (8 ones leave two blocks, 32 join a third) until a block runs
  out and an epoch rebuilds: era-family plus inequality invariant.
- 1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD (Quadratic Mess): two-sided bouncer on 1000|0001 blocks, main regime proved
  for all sizes, rebuilt with about three times as many 0001s: candidate for a closed family with ratio invariant.
- 1RB0RE_1LC1RA_1LD0LC_0RE0LA_1RA1RF_0RA--- (G12, Shift-overflow counter like 86): two-level counter on 0 1^(odd)
  words, run of 1s grows by 2 per round in doubling time, full rewrites at 1.7e6 and 2.6e7 steps: PR 86's
  token engine + window search.
- 1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB--- (G12, Shift-overflow counter): word of blocks with last block growing by
  2 in doubling time, halting only at rare left-end rebuilds: same as above (weaker evidence; whether a window ever
  appears is unknown).
