"""The counter phases of 1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA, with the exact simulator of hybrid.py.

usage: python3 resets.py DIGITS [MACHINE]    run up to 10^DIGITS steps; print, at each reset, the last configuration of the
                                    counter phase and the first one after it (number of digits of the step, tape)
"""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hybrid  # noqa: E402


def main(digits, machine=hybrid.M):
    prev, last, t0 = None, None, time.time()
    for t, c in hybrid.events(10 ** digits, machine=machine):
        f = c.split()[1]
        a = int(f.split("^")[1]) if "^" in f else 1
        if prev is not None and a != prev + 2:
            print(len(str(last[0])), last[1])
            print(len(str(t)), c, f"[{time.time() - t0:.0f}s]", flush=True)
        prev, last = a, (t, c)


if __name__ == "__main__":
    main(int(sys.argv[1]), *sys.argv[2:3])
