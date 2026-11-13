"""The first run of the tape matters only through its length mod 4: every way of entering it, for every length.

The left part of the tape is blank, then a run of n alternating cells.  The head can step onto the last cell of the
run from the right in five states (A, B, C, D, F: the states a left move leads to), and that cell is 0 or 1: ten
entries.  For each entry this script simulates the excursion (until the head steps out to the right of where it came
in, or halts) and

  check   compares, for every n from 1 to NMAX, the excursion for n with the one for n + 4: both halt, or the same
          exit state, the same change of the length of the first run and the same cells left between the run and
          the head.  Prints the entries and lengths where that fails (only n = 1 and n = 2) and the table of
          outcomes.
  lean    writes lean/Shift4.lean: one theorem per entry (and per n mod 4 where the head sweeps to the left end),
          proved along the symbolic run of tools/py/bbtools/symtm.py for every value of the parameter a.  A bounce
          is stated with any tape L to the left of the cells it touches; a sweep with the whole run (4a + c cells).
          The outcome for a + 1 is the outcome for a with one more copy of a 4-cell word: that is the statement
          "a shift by 4 changes nothing else".

usage (from the repo root):
  python3 holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/shift4.py check [NMAX]
  python3 holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/shift4.py lean > holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/lean/Shift4.lean
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))

M = "1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---"
T = {}
for _s, _part in enumerate(M.split("_")):
    for _r in range(2):
        _x = _part[3 * _r:3 * _r + 3]
        T[(_s, _r)] = None if _x[2] == "-" else (int(_x[0]), 1 if _x[1] == "R" else -1, ord(_x[2]) - 65)
ENTRY = sorted({t[2] for t in T.values() if t and t[1] == -1})     # states after a left move
NAMES = "ABCDEF"


def alt(n, last):
    """n alternating cells, left to right, the last one `last`."""
    return [last ^ ((n - 1 - i) & 1) for i in range(n)]


def excursion(n, last, q, limit=10 ** 7):
    """Blank, then alt(n, last) on cells 0..n-1; the head on cell n-1 in state q (on cell -1 if n = 0).  Runs until
    the head is on cell n or the machine halts.  Returns (kind, state, cells from the leftmost visited one, lowest
    cell reached, steps)."""
    cells = dict(enumerate(alt(n, last)))
    pos, st, steps, low = n - 1, q, 0, n - 1
    while pos < n:
        t = T[(st, cells.get(pos, 0))]
        if t is None:
            return "halt", st, None, low, steps + 1
        cells[pos] = t[0]
        pos += t[1]
        st = t[2]
        steps += 1
        low = min(low, pos)
        if steps > limit:
            return "loop", st, None, low, steps
    lo = min(min(cells), 0) if cells else 0
    return "exit", st, [cells.get(i, 0) for i in range(lo, n)], low, steps


def summary(n, last, q):
    """Outcome of an entry as (kind, exit state, change of the length of the first run, cells between the run and the
    head, last cell of the run).  The first run is the maximal alternating stretch from the leftmost visited cell."""
    k, st, cells, low, steps = excursion(n, last, q)
    if k != "exit":
        return (k,)
    r = 1
    while r < len(cells) and cells[r] != cells[r - 1]:
        r += 1
    return (k, st, r - n, tuple(cells[r:]), cells[r - 1])


def related(n, last, q):
    """The entries for n and n + 4 have the same outcome: both halt, or the same exit state, the same change of the
    run length and the same cells between the run and the head."""
    return summary(n, last, q) == summary(n + 4, last, q)


def check(nmax):
    bad = []
    print("entry (state, last cell of the run): outcome for n = 4a + 8 .. 4a + 11 (a large): exit state, change of the"
          " run length, cells left between the run and the head, kind")
    for last in (0, 1):
        for q in ENTRY:
            for n in range(1, nmax + 1):
                if not related(n, last, q):
                    bad.append((NAMES[q], last, n))
            row = []
            for n in range(400, 404):
                k, st, cells, low, steps = excursion(n, last, q)
                if k != "exit":
                    row.append(k)
                    continue
                r = 1
                while r < len(cells) and cells[r] != cells[r - 1]:
                    r += 1
                row.append("%s %+d [%s] %s" % (NAMES[st], r - n, "".join(map(str, cells[r:])), "sweep" if low < 0 else "bounce"))
            print("  %s on %d:  %s" % (NAMES[q], last, " | ".join(row)))
    print("lengths 1..%d compared with n + 4, 10 entries each; not related: %s" % (nmax, bad))
    ok = all(n <= 2 for _, _, n in bad)
    print("ALL CHECKS PASS (a shift by 4 is invisible for every entry and every n >= 3)" if ok else "FAILED")
    return ok


def cellstr(cs):
    return " ".join(map(str, cs))


def theorems():
    from bbtools.symtm import prove, ProofError
    out, failed = [], []
    for last in (0, 1):
        for q in ENTRY:
            k, st, cells, low, steps = excursion(400, last, q)
            if k != "exit":
                continue                      # an immediate halt (F on 1): the same for every length
            if low >= 0:                      # a bounce: only the cells low..n-1 are touched
                n = 400
                before = alt(n, last)[low:]
                after = cells[len(cells) - (n - low):]
                name = "enter_%s%d" % (NAMES[q], last)
                start = "L %s %s> %d R" % (cellstr(before[:-1]), NAMES[q], before[-1])
                end = "L %s %s> R" % (cellstr(after), NAMES[st])
                doc = ("%s steps onto the last cell of an alternating stretch, a %d, and comes back out in %s after "
                       "%d steps, having looked at its last %d cells only (any tape L further left)."
                       % (NAMES[q], last, NAMES[st], steps, n - low))
                try:
                    out.append(prove(M, name, start, end, doc=doc, rotate=True, count_first=True, max_seg=40)[0])
                except ProofError as e:
                    failed.append(str(e))
                continue
            for c in range(1, 5):             # a sweep: run of 4(a+1) + c cells
                def left_after(a):
                    kk, s2, cl, lw, stp = excursion(4 * (a + 1) + c, last, q)
                    return s2, cl
                s5, e5 = left_after(5)
                s6, e6 = left_after(6)
                s7, e7 = left_after(7)
                suf = 0
                while suf < len(e5) - 4 and e5[-1 - suf] == e6[-1 - suf]:
                    suf += 1
                suf = min(suf, 12)
                S = e5[len(e5) - suf:]
                W = e6[len(e6) - suf - 4:len(e6) - suf]
                P = e5[:len(e5) - suf]
                kcopies = 0
                while len(P) >= 4 and P[-4:] == W:
                    P = P[:-4]
                    kcopies += 1
                while len(S) >= 4 and S[:4] == W:
                    S = S[4:]
                    kcopies += 1
                assert kcopies >= 5 and s5 == s6 == s7 and e7 == P + W * (kcopies + 2) + S, (q, last, c)
                j = kcopies - 5
                run = alt(4 * (5 + 1) + c, last)
                W0 = run[:4]
                tail = run[4 * 6:]
                name = "enter_%s%d_r%d" % (NAMES[q], last, c % 4)
                start = "0^inf (%s)^a+1 %s %s> %d R" % ("".join(map(str, W0)), cellstr(tail[:-1]), NAMES[q], tail[-1])
                end = "0^inf %s (%s)^a+%d %s %s> R" % (cellstr(P), "".join(map(str, W)), j, cellstr(S), NAMES[s5])
                doc = ("%s steps onto the last cell, a %d, of the first run of 4a + %d cells (blank tape to its left), "
                       "sweeps to the left end, turns and comes back out in %s.  The run comes out as `%s (%s)^(a+%d) %s`: "
                       "one more copy of a 4-cell word for a + 1."
                       % (NAMES[q], last, 4 + c, NAMES[s5], cellstr(P), "".join(map(str, W)), j, cellstr(S)))
                try:
                    out.append(prove(M, name, start, end, doc=doc, rotate=True, count_first=True, max_seg=40)[0])
                except ProofError as e:
                    failed.append(str(e))
    return out, failed


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "lean":
        from bbtools.symtm import rules_file
        ths, failed = theorems()
        if failed:
            sys.stderr.write("\n".join(failed) + "\n")
            sys.exit(1)
        ns = next(l.split()[1] for l in open(os.path.join(HERE, "..", "lean", "Machine.lean")) if l.startswith("namespace "))
        doc = ("# A shift of the first run by 4 cells\n\nGenerated by `py/shift4.py`; do not edit by hand.  Every way the head can "
               "enter the first run of the tape (an alternating run with blank tape to its left) from the right: the "
               "bounces for any tape further left, the sweeps for every length 4a + c.  See the README, section "
               "\"One run for four machines\".")
        sys.stdout.write(rules_file("Machine", ns, ths, doc))
    else:
        nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 200
        sys.exit(0 if check(nmax) else 1)


if __name__ == "__main__":
    main()
