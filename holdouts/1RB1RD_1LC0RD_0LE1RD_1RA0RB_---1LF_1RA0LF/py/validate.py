"""Validation of the two accelerated simulators of 1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF.

1. c/accsim.c with accel=0 is a plain simulator (one cell per step); with accel=1 it uses runs and shift rules.
   Both must give the same step count at the same events (here 2^16 and 2^18 events).
2. c/accbig.c adds jumps over linear regimes and big integers. Stopped exactly at an event number (TARGET) it must
   give the step count of accsim at that event (here 2^20, 2^24 and 2^26 events: 13, 49 and 80 cycle jumps).
The longer comparisons made for the README (2^30 events = 2.3*10^17 steps against accsim, 172 cycle jumps; and
3.66*10^18 events against a second implementation of the jumps with 64-bit counts and capped jump lengths) are
listed there.

usage: python3 validate.py [dir for the binaries, default /tmp]
"""
import os
import re
import subprocess
import sys

M = "1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF"
HERE = os.path.dirname(os.path.abspath(__file__))


def main():
    out = sys.argv[1] if len(sys.argv) > 1 else "/tmp"
    sim, big = os.path.join(out, "accsim"), os.path.join(out, "accbig")
    subprocess.check_call(["gcc", "-O2", "-o", sim, os.path.join(HERE, "../c/accsim.c")])
    subprocess.check_call(["gcc", "-O2", "-o", big, os.path.join(HERE, "../c/accbig.c")])

    def steps_sim(events, accel):
        o = subprocess.run([sim, M, str(events), str(accel), "3", "11"], capture_output=True, text=True).stdout
        return int(re.search(r"event %d steps (\d+)" % events, o).group(1))

    def steps_big(events):
        o = subprocess.run([big, M, "160", "100000000", "3", "11"], capture_output=True, text=True,
                           env={"TARGET": str(events)}).stdout
        m = re.search(r"event %d steps (\d+) cyclejumps (\d+)" % events, o)
        return int(m.group(1)), int(m.group(2))

    for e in (1 << 16, 1 << 18):
        a, b = steps_sim(e, 0), steps_sim(e, 1)
        assert a == b, (e, a, b)
        print("plain = shift rules at event %d: %d steps" % (e, a))
    for e in (1 << 20, 1 << 24, 1 << 26):
        a = steps_sim(e, 1)
        b, j = steps_big(e)
        assert a == b, (e, a, b)
        print("shift rules = cycle jumps at event %d: %d steps (%d cycle jumps)" % (e, a, j))
    print("OK")


if __name__ == "__main__":
    main()
