"""Search small macro configurations of regular gadgets from which the machine halts.

usage: python3 witness_search.py [MAXSTEPS]     (default 3e6; compiles ../c/hsearch.c with gcc)

Candidates: the head in D on `b^6 G1 b^n1 [G2 b^n2 [G3 b^n3]] g0` (b = 1000), Gi among g0..g4 and s, ni in {0, 2, 5}.
Prints, for each halting candidate, the steps before the halting step and the macro form, then the shortest ones
without empty blocks (with and without s).
"""
import itertools
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
M = os.path.basename(os.path.dirname(HERE))
G = {"g0": "1001", "g1": "1001100", "g2": "100110", "g3": "10011", "g4": "10010", "s": "0"}
lines = []
for n in (1, 2, 3):
    for gs in itertools.product(G, repeat=n):
        for bs in itertools.product((0, 2, 5), repeat=n):
            s = "1000" * 6 + "".join(G[g] + "1000" * b for g, b in zip(gs, bs)) + "1001"
            macro = "6 " + " ".join(f"{g} {b}" for g, b in zip(gs, bs)) + " g0"
            lines.append(macro.replace(" ", "_") + " " + s)
exe = os.path.join(tempfile.mkdtemp(), "hsearch")
subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(HERE, "..", "c", "hsearch.c")], check=True)
out = subprocess.run([exe, M, sys.argv[1] if len(sys.argv) > 1 else "3000000"], input="\n".join(lines) + "\n",
                     capture_output=True, text=True).stdout.split("\n")
hs = [(int(l.split()[1]), l.split()[2].replace("_", " ")) for l in out if l.startswith("HALT")]
print(f"{len(hs)} of {len(lines)} candidates halt")
nz = sorted(h for h in hs if " 0 " not in h[1])
print("shortest without empty blocks:", nz[:3])
print("shortest without empty blocks or s:", [h for h in nz if " s " not in h[1]][:3])
