"""The phases of 1RB0RE_0LC1LE_0RD1LD_1RA1LF_1LC0RA_0LB---: a Collatz-like map Z -> 3Z/2 + c beside a data word D.

usage: python3 phases.py [PHASES]        (default 300; compiles ../c/nextps.c)

A phase starts at PS(D, Z): the word D (a few dozen cells, starting `0 1` at the fixed left end of the tape), then
Z zeros, then `1 0 0`, the head in state E on the blank cell after it.  During the phase a wall of `100` words grows
right from the `1 0 0` while the zeros are eaten from the right, four per sweep (lean/Rules.lean, `sweep`); when they
run out the head works on D and the wall turns back into zeros: PS(D', Z') with Z' = 3Z/2 + c.

`nextps` runs the machine (the C program) from PS(D, Z) to the next PS.  `phase(D, Z)` gets PS(D', Z') for any Z: it
runs `nextps` on three Z0 = base, base + 4, base + 8 of the same residue Z mod 4, checks that D' is the same and that
Z0' grows by 6 per 4, and extrapolates (linearity in Z is checked at three points, not proved).

1. checks `phase` against the plain machine for the phases from blank tape to step 8.7e7 (BLANK below);
2. iterates `phase` from the first of them for PHASES phases, printing D whenever it takes a new shape.
"""
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
EXE = "/tmp/m4_nextps"
# (step, D, Z) of the phase starts from blank tape, from the plain simulator
BLANK = [(457, "0100101", 15), (827, "010101001", 21), (1559, "010101001", 33), (3137, "010101001", 51),
         (6387, "01101001001", 75), (13851, "01000000000001", 114), (29353, "010000000000101", 171),
         (63185, "01000000000101001", 255), (137733, "0100000000101001001", 381),
         (304785, "0100000000101001001", 573), (679773, "0100000000101001001", 861),
         (1522185, "0100000000101001001", 1293), (3415653, "0100000000101001001", 1941),
         (7673025, "0100000000101001001", 2913), (17247723, "0100000000101001001", 4371),
         (38764591, "010000000101001001001", 6555), (87138125, "01000000101001001001001", 9831)]


def build():
    if not os.path.exists(EXE):
        subprocess.run(["gcc", "-O2", "-o", EXE, os.path.join(HERE, "..", "c", "nextps.c")], check=True)


def nextps(d, z):
    out = subprocess.run([EXE], input=f"{d} {z}", capture_output=True, text=True).stdout.split()
    if out[0] == "halt":
        return ("halt", int(out[1]))
    return (out[0], int(out[1]), int(out[2]))


_cache = {}


def phase(d, z):
    key = (d, z % 4)
    if key not in _cache:
        base = 4 * (len(d) + 12) + z % 4
        res = [nextps(d, b) for b in (base, base + 4, base + 8)]
        if any(r[0] == "halt" for r in res):
            _cache[key] = ("halt",)
        else:
            assert len({r[0] for r in res}) == 1, res
            assert res[1][1] - res[0][1] == 6 and res[2][1] - res[1][1] == 6, res
            _cache[key] = ("lin", base, res[0][1], res[0][0])
    v = _cache[key]
    if v[0] == "halt":
        return v
    _, base, img, nd = v
    return (nd, img + 3 * (z - base) // 2)


def short(d):
    s = re.sub(r"(?:001){2,}", lambda m: f" (001)^{len(m.group()) // 3} ", d)
    return re.sub(r"0{4,}", lambda m: f" 0^{len(m.group())} ", s).strip()


def main():
    sys.set_int_max_str_digits(0)
    build()
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    for (_, d, z), (_, d2, z2) in zip(BLANK, BLANK[1:]):
        assert nextps(d, z)[:2] == (d2, z2)
        assert phase(d, z) == (d2, z2), (d, z)
    print(f"phase() and the machine agree on the {len(BLANK) - 1} phases from blank tape to step {BLANK[-1][0]}")
    _, d, z = BLANK[0]
    counts = [0] * 4
    for i in range(n):
        v = phase(d, z)
        if v[0] == "halt":
            print(f"HALT in phase {i}: D = {short(d)}, Z mod 4 = {z % 4}")
            return
        counts[z % 4] += 1
        if v[0] != d:
            print(f"  phase {i + 1}: D = {short(v[0])} (from Z mod 4 = {z % 4}; Z has {len(str(z))} digits)")
        d, z = v
    print(f"no halt in {n} phases; Z has {len(str(z))} digits; phases by Z mod 4: {counts}")


if __name__ == "__main__":
    main()
