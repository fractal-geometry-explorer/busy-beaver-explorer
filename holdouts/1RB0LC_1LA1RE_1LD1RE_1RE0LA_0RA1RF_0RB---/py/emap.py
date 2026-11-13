"""The C-event map of 1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB--- (single-number part only).

Sample the run when the head is in state C at the left end of the tape.  The tape is then mostly one of

    X(n, t) = C> 000 (100)^n T        Y(n, t) = C> (100)^n T        T = 1 (t = 0) or 101 (t = 1)

and between X/Y-events there are events Z(n) = C> 00 11 (001)^n T' (just after a Y-event) and, after a Y-event with
n odd, a nested phase C> 000 (10)^2 (010)^y T', C> (100)^3 (010)^y' T', C> 00 11 (001)^2 0 11 (001)^y' T', ...
The single-number rules are

    X(n, t), n odd   ->  X((3n+5)/2, t')         X(n, t), n even  ->  Y((3n+6)/2, t')     t' = t xor [n mod 4 in {0, 1}]
    Y(n, t), n even  ->  X((3n+4)/2, t')                                                   t' = t xor [n mod 4 = 0]

Y(n, t) with n odd starts the nested phase: a second number y = (3n+3)/2 appears; when the next one, y' = y - 1 or
y + 1, is even the phase ends at X(3y'/2 + 6), otherwise it nests deeper.  That part of the map is not yet written
down, so `blank` checks only the X/Y-events that follow the single-number rules and lists the others.

usage: python3 emap.py blank STEPS      the C-events of the blank run, with the single-number rules checked
       python3 emap.py search NMAX      direct runs from X(n, t) and Y(n, t), n < NMAX, for 10^8 steps: any halt?
"""
import os, re, sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..",
                                "1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---", "py"))
import g01tools as g  # noqa: E402

M = "1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---"
PX = re.compile(r"C000((?:100)*)(1|101)")
PY = re.compile(r"C((?:100)+)(1|101)")


def parse(t):
    for nm, p in (("X", PX), ("Y", PY)):
        m = p.fullmatch(t)
        if m:
            return nm, len(m.group(1)) // 3, 0 if m.group(2) == "1" else 1
    return None


def step(f, n, t):
    """next X/Y-event by the single-number rules, or None (Y with n odd: nested phase)"""
    if f == "X":
        t2 = t ^ (n % 4 in (0, 1))
        return ("X", (3 * n + 5) // 2, t2) if n % 2 else ("Y", (3 * n + 6) // 2, t2)
    if n % 2:
        return None
    return ("X", (3 * n + 4) // 2, t ^ (n % 4 == 0))


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "blank":
        prev, ok, other = None, 0, 0
        for k, tape in g.events(M, "A> 0", int(float(sys.argv[2])), "C", "L"):
            if isinstance(tape, int):
                print(k, tape)
                break
            p = parse(tape)
            if p is None:
                other += 1
                print(k, g.show(tape)[:120], "(not an X/Y-event)")
                continue
            if prev and step(*prev) is not None:
                assert step(*prev) == p, (prev, p, step(*prev))
                ok += 1
            elif prev:
                print("   nested phase from", prev, "to", p)
            prev = p
            print(k, *p, flush=True)
        print(f"blank: {ok} X/Y-events follow the single-number rules from the one before; {other} other events")
    elif cmd == "search":
        for f in "XY":
            for T in ("1", "101"):
                for n in range(int(f == "Y"), int(sys.argv[2])):
                    tape = ("C> 000 (100)^%d %s" if f == "X" else "C> (100)^%d %s") % (n, " ".join(T))
                    *_, last = g.events(M, tape, 10**8, "C", "L", 0)
                    if last[0] == "halted":
                        print("HALT", f, n, T, last[1])
        print("search done")
