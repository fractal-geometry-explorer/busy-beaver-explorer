  **The 64-digit tree, rerun with checked arithmetic (October 24, afternoon; `rtree3d`, 64 parts at split level 20,
  `../rt3/c64d/`, about 16 CPU hours over three restarts).** No path was dropped as invalid this time; 113,555 paths
  of total measure 8.1 × 10⁻¹⁵ stopped at a coefficient overflow and are counted as undecided. Entry measure
  2.072721 × 10⁻³, undecided 4.141 × 10⁻¹⁰, largest ceiling 54.249 (63 digits, the R₁ ≡ 12 (mod 16) route), then 52.855
  (61 digits), 49.003 (64), 48.633 (61), 47.611 (61); among the entries decided within 62 digits the largest ceiling is
  52.855. The tree has 5,983,365 entries of ceiling ≥ 20, the same count as the provisional run, and the exact
  candidate check over all of them at every width from 2^17 to each entry's lock limit finds CANDIDATES. So the 62- and
  64-digit figures above stand without the arithmetic caveat; the 62-digit tree is not rerun separately, because every
  route decided within 62 digits is an entry of the 64-digit tree with at most 62 digits.
  *What the routes to late entries are made of* (`passtail.py` over the 5,983,365 entries): an entry whose route
  contains no round of the extra-wall loop has ceiling at most 33.63; the highest ceilings sit on routes with about 20
  such rounds (54.25 with 20, 52.85 with 21, 49.00 with 19), and every ceiling above 41.6 has at least 8. Complete
  passes of the extra-wall loop (the 8-round words P or Q) are rarer than pieces: 2,401 entries have one complete
  pass on the way (1,454 through P, 947 through Q; measure 6.5 × 10⁻¹⁴ in all) and one entry has two (P P, ceiling
  47.10, measure 2⁻⁶⁴); by ceiling bucket the one-pass routes carry 30 to 50% of the measure from 40 upward (3.4 versus
  1.5 × 10⁻¹⁴ at 40–44, 6.0 versus 3.7 × 10⁻¹⁷ at 44–48), and none below 20 is counted.
