# Frame-map hunts

Two machines whose Lean files prove a frame-map reduction (`lean/Phases.lean`: the machine halts from blank tape
iff the orbit of the start frame under `next` reaches a `none` case):

- `1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE`, start `Ph.g 0 1`
- `1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD`, start `Ph.z 0 0 2`

`gen.py` reads `next` straight from the Lean file and writes the rule table (`<machine>.h`); it also has an
unaccelerated Python reference (`ref_step`). `frames.c` follows the map, repeating shift cycles of up to 6 rules in
bulk while every pattern test along the cycle is provably constant (see the comment at its top). `run.sh` builds both.

**Checks.** For both machines: `frames N print` agrees with `gen.py`'s reference on the first 200000 frames;
the frame after 3 million steps agrees with Lean's own `#eval iter` of the extracted `next`; and the accelerated
run agrees with the plain one (`frames N plain`) at about 10^9 frames.

**Result (21 November 2026).** No halt in 10^19 frames for either machine (Lean's `no_halt_phases` covers 10^8).
The arguments grow like the square root of the frame count: at 10^19 frames the largest is about 1.4e10 for the
first machine and 1.1e10 for the second. Runs took 83 and 112 minutes on one core.
