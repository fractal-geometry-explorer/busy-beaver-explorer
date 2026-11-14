"""The counter list of 1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF, read off the exact accelerated simulator.

The tape is  prefix (00000001010)^bulk  list : the list is made of counters (101)^c separated by short words.
Every `every` events (an event is a new cell at the left end) this prints the event, the step count, the bulk and
the list with each run (101)^c, c >= 2, written as the number c; by default only when the separators change (a
reorganisation), with a fourth argument at every sample.

usage: python3 counters.py ACCSIM START EVERY END [all]
       e.g.  gcc -O2 -o /tmp/accsim ../c/accsim.c && python3 counters.py /tmp/accsim 160000 160 164000 all
"""
import re
import subprocess
import sys

M = "1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF"
BULK = "00000001010"


def expand(s):
    return re.sub(r"\((\d+)\)\^(\d+) ", lambda m: m.group(1) * int(m.group(2)), s)


def tokens(lst):
    res, i, lit = [], 0, ""
    while i < len(lst):
        m = re.match(r"(?:101){2,}", lst[i:])
        if m:
            if lit:
                res.append(lit)
                lit = ""
            res.append(len(m.group(0)) // 3)
            i += len(m.group(0))
        else:
            lit += lst[i]
            i += 1
    if lit:
        res.append(lit)
    return res


def samples(accsim, start, every, end):
    out = subprocess.run([accsim, M, str(end), "1", "3", "11"], capture_output=True, text=True,
                         env={"TRACE": "%s:%s" % (start, every)}).stdout
    for line in out.split("\n"):
        if not line.startswith("T "):
            continue
        _, ev, steps, rest = line.split(" ", 3)
        m = max(re.finditer(r"\((%s)\)\^(\d+) " % BULK, rest), key=lambda m: int(m.group(2)))
        yield int(ev), int(steps), int(m.group(2)), tokens(expand(rest[m.end():]).rstrip("0"))


def main():
    accsim, start, every, end = sys.argv[1:5]
    prev = None
    for ev, steps, bulk, t in samples(accsim, start, every, end):
        shape = tuple(x for x in t if isinstance(x, str))
        if shape != prev or len(sys.argv) > 5:
            print(ev, steps, bulk, " ".join(str(x) for x in t))
        prev = shape


if __name__ == "__main__":
    main()
