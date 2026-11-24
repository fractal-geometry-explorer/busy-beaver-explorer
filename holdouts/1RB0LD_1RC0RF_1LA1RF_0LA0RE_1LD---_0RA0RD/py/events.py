"""Summaries of an event log of py/oacc.py (OEVENTS=FILE: one line `sweeps steps digits...` each time the number of
digits or the list of odd walls changes) (24 November 2026).

    python3 py/events.py decades FILE [FILE...]       the first line of each new power of 10 of the step count
    python3 py/events.py window LO HI FILE [FILE...]  every line between steps LO and HI where the shape of the
                                                      first five digits changes (a collapse at the far end)
Files may be gzipped; lines out of order (from a restarted run) are skipped.
"""
import gzip
import re
import sys


def lines(files):
    last = None
    for fn in files:
        f = gzip.open(fn, 'rt') if fn.endswith('.gz') else open(fn)
        for line in f:
            w = line.split()
            T = int(w[1])
            if last is not None and T <= last:
                continue
            last = T
            yield T, w


def decades(files):
    dec = None
    for T, w in lines(files):
        if len(str(T)) != dec:
            dec = len(str(T))
            print('%.3e n=%d  %s ... %s' % (T, len(w) - 4, ' '.join(w[2:9]), ' '.join(w[-4:])))


def window(lo, hi, files):
    prev = None
    for T, w in lines(files):
        if T < lo or T > hi:
            continue
        key = tuple(re.sub(r'\[\d+\]', '[]', x) for x in w[2:7]) + tuple(len(x) for x in w[2:7])
        if key != prev:
            print('%.6e' % T, ' '.join(w[2:7]))
            prev = key


if __name__ == '__main__':
    if sys.argv[1] == 'decades':
        decades(sys.argv[2:])
    else:
        window(float(sys.argv[2]), float(sys.argv[3]), sys.argv[4:])
