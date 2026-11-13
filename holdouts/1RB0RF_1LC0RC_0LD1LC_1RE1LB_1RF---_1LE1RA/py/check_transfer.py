"""Check c/transfer.c against the plain machine.

Both runs print a hash of the tape at every configuration with the head in C at the left end (CHECK=1).  The run
that applies the transfer rule in closed form must pass through a subset of the plain run's configurations, at the
same step counts.

usage: python3 check_transfer.py [STEPS]     (default 300000000)
"""
import os
import subprocess
import sys
import tempfile

here = os.path.dirname(os.path.abspath(__file__))
steps = sys.argv[1] if len(sys.argv) > 1 else "300000000"
exe = os.path.join(tempfile.gettempdir(), f"transfer_{os.getuid()}")
subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(here, "..", "c", "transfer.c")], check=True)
env = dict(os.environ, CHECK="1")
plain = subprocess.run([exe, steps, "600", "20", "plain"], env=env, capture_output=True, text=True).stdout.split("\n")
fast = subprocess.run([exe, steps, "600", "20"], env=env, capture_output=True, text=True).stdout.split("\n")
P = {l for l in plain if l.startswith("G ")}
F = [l for l in fast if l.startswith("G ")]
bad = [l for l in F if int(l.split()[1]) <= int(steps) and l not in P]
print(f"plain run: {len(P)} left-end configurations in {steps} steps; accelerated run: {len(F)}, "
      f"{len(bad)} not on the plain run")
sys.exit(1 if bad or not F else 0)
