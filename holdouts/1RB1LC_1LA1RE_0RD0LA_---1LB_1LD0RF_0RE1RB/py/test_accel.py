"""Test of accel.py against the plain C simulator.
python3 holdouts/<M>/py/test_accel.py [STEPS]     (default 6*10^9 steps, about a minute)

tools/c/tmrun.c lists every moment where the head, in state C, is at the left end of the tape; at those where it
reads 0 (the overflow events) the accelerated simulator must give the same step count, z and word W, and its learned
tick costs must never disagree with a directly simulated tick.
"""
import os, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "../../..")
M = "1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB"


def main():
    n = int(float(sys.argv[1])) if len(sys.argv) > 1 else 6 * 10 ** 9
    with tempfile.TemporaryDirectory() as d:
        exe, ev = os.path.join(d, "tmrun"), os.path.join(d, "events.txt")
        subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(ROOT, "tools/c/tmrun.c")], check=True)
        with open(ev, "w") as f:
            subprocess.run([exe, M, str(n), "at", "C", "L", "100000"], stdout=f, check=True)
        r = subprocess.run([sys.executable, os.path.join(HERE, "accel.py"), "check", ev])
    print("ok" if r.returncode == 0 else "FAILED")
    sys.exit(r.returncode)


if __name__ == "__main__":
    main()
