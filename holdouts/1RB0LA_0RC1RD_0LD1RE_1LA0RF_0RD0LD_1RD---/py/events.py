"""The A-events of 1RB0LA_0RC1RD_0LD1RE_1LA0RF_0RD0LD_1RD--- (partial analysis).

Sample the run when the head is in state A at the left end on `00 1`: the tape is then a list of blocks, e.g.

    X(n)    = A> 00 (10)^n 01
    Y(a, b) = A> 00 1010 (010)^a (10)^b 01
    A> 00 (10)^1529 (010)^1529 00 (10)^4585 (01)^2 00 1, ...

Two rules are clear:  X(n), n even  ->  Y(n/2 - 1, 3n/2)   and   Y(a, b), a odd  ->  X(b + (3a + 11)/2),
so X(n) with n = 0 mod 4 goes to X((9n + 16)/4).  Other cases (X(n) with n odd, Y(a, b) with a even) start longer
block lists, not yet described.  `blank` prints the events of the blank run and checks the two rules where they
apply.

usage: python3 events.py blank STEPS
"""
import os, re, sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..",
                                "1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---", "py"))
import g01tools as g  # noqa: E402

M = "1RB0LA_0RC1RD_0LD1RE_1LA0RF_0RD0LD_1RD---"
PX = re.compile(r"A00((?:10)*)01")
PY = re.compile(r"A001010((?:010)*)((?:10)*)01")


def parse(t):
    m = PX.fullmatch(t)
    if m:
        return ("X", len(m.group(1)) // 2)
    m = PY.fullmatch(t)
    if m:
        return ("Y", len(m.group(1)) // 3, len(m.group(2)) // 2)
    return None


def step(e):
    if e[0] == "X" and e[1] % 2 == 0 and e[1] >= 2:
        a, b = e[1] // 2 - 1, 3 * e[1] // 2
        return ("Y", a, b) if a > 0 else ("X", b + 2)     # Y(0, b) is X(b + 2)
    if e[0] == "Y" and e[1] % 2 == 1:
        return ("X", e[2] + (3 * e[1] + 11) // 2)
    return None


if __name__ == "__main__":
    prev, ok = None, 0
    for k, t in g.events(M, "A> 0", int(float(sys.argv[2])), "A", "L"):
        if isinstance(t, int):
            print(k, t)
            break
        if not t.startswith("A001"):
            continue
        e = parse(t)
        if prev is not None and step(prev) is not None:
            assert step(prev) == e, (prev, e)
            ok += 1
        prev = e
        print(k, e if e else "", g.show(t)[:150], flush=True)
    print(f"blank: {ok} events follow one of the two rules from the one before")
