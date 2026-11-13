"""Counts from one long run of a machine of the wall-counter family (see the README): samples, overflows, mergers,
how often E reads a 1, and the tape at the last sample, as JSON.  Compiles and runs ../c/walls.c.

usage: python3 walls.py MACHINE STEPS > stats.json
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "..", "c", "walls.c")
BIN = os.path.join(HERE, "..", "c", "walls")

if __name__ == "__main__":
    if not os.path.exists(BIN) or os.path.getmtime(BIN) < os.path.getmtime(SRC):
        subprocess.check_call(["gcc", "-O2", "-o", BIN, SRC])
    sys.stdout.write(subprocess.check_output([BIN, sys.argv[1], sys.argv[2]]).decode())
