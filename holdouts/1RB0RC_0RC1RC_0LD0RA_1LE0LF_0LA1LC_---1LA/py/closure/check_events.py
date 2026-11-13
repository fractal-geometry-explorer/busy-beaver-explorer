"""Compare the accelerated simulator with the plain C simulator, event by event.

usage: python3 holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/py/closure/check_events.py EVENTS_FILE [--plain]
EVENTS_FILE: output of `c/events MACHINE MAXSTEPS` (lines: steps ones width crc32).  Every event the accelerated
simulator stops at (all of them with --plain; with cycle rules, those not jumped over) must be in the file with the
same step count and the same tape (number of ones, width, crc32 of the cells between the first and the last 1).
"""
import sys
import zlib
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import accel as acc2


def main(argv):
    ref = {}
    last = 0
    for line in open(argv[1]):
        f = line.split()
        if len(f) == 4:
            ref[int(f[0])] = (int(f[1]), int(f[2]), int(f[3]))
            last = int(f[0])
    d = acc2.Driver(None, '--plain' not in argv)
    n = [0, 0]

    def on_event(d, toks):
        if d.s.steps > last:
            return True
        cells = ''.join(str(t) if isinstance(t, int) else '' if t == 'H' else ''.join(map(str, t[0])) * t[1]
                        for t in toks).strip('0')
        got = (cells.count('1'), len(cells), zlib.crc32(cells.encode()))
        if ref.get(d.s.steps) != got:
            print("MISMATCH at step", d.s.steps, got, ref.get(d.s.steps))
            n[1] += 1
        n[0] += 1
        return n[1] > 5

    d.run(None, on_event)
    print("events compared: %d of %d in the file, mismatches: %d, jumps: %d, cycle rules: %d"
          % (n[0], len(ref), n[1], d.jumps, d.nrules))
    return 1 if n[1] else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
