"""Writes lean/MacroRules.lean: the local pieces of one visit of 1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD---, for every
length and every surrounding tape, each proved by bbtools.symtm (shift rules, `rfl`, `omega`); lean/Macro.lean puts
them together for every counter list.

A counter c is (10)^c, written (1010)^b+1 for c = 2b + 2 and (1010)^b 1 0 for c = 2b + 1.  The pieces:
  start_*  : the visit (A at the right end) to the head on the separator left of the last counter k, in D (k even) or
             E (k odd), the counter's cells turned into 1^(2k+4);
  cross_*  : E on a separator 0 crosses the counter left of it, to the next separator, in D (even) or E (odd);
  turn_*   : E on a separator 1 or D on a separator 0: the counter left of it loses one and the head turns right in C;
  ret_*    : C crossing 1^(2j+1) 0 1 back to the right (restoring the counters), and at the end 1^(2j+1) to the visit.

usage: python3 macro.py > ../lean/MacroRules.lean
       python3 macro.py check N     the Lean rule `ordinary` (mirrored here) against counters.py on N random lists
                                    and on the first N visits from blank tape (equal tapes; `none` exactly at rebuilds)
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.symtm import prove, rules_file

M = "1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD---"
NS = "H16609"

RULES = []
for s in "01":
    RULES += [
        (f"start_e{s}", f"k = 2a+2, separator {s}: D on the separator.",
         f"L {s} (1010)^a+1 A> 0^inf", f"L D> {s} (1111)^a+2 0^inf"),
        (f"start_o{s}", f"k = 2a+1, separator {s}: E on the separator.",
         f"L {s} (1010)^a 1 0 A> 0^inf", f"L E> {s} 1 1 (1111)^a+1 0^inf"),
        (f"cross_z{s}", f"E on a separator 0 crosses a counter 0 (next separator {s}).",
         f"L {s} E> 0 R", f"L D> {s} 0 R"),
        (f"cross_e{s}", f"E on a separator 0 crosses c = 2b+2 (next separator {s}).",
         f"L {s} (1010)^b+1 E> 0 R", f"L D> {s} (1111)^b+1 0 R"),
        (f"cross_o{s}", f"E on a separator 0 crosses c = 2b+1 (next separator {s}).",
         f"L {s} (1010)^b 1 0 E> 0 R", f"L E> {s} 1 1 (1111)^b 0 R"),
    ]
    for q, w in (("E", "1"), ("D", "0")):
        RULES += [
            (f"turn{q}_o{s}", f"{q} on a separator {w}, counter c+1 = 2b+1 left of it: it loses one, C turns right.",
             f"L {s} (1010)^b 1 0 {q}> {w} R", f"L {s} (1010)^b 0 1 C> 1 R"),
            (f"turn{q}_e{s}", f"{q} on a separator {w}, counter c+1 = 2b+2 left of it: it loses one, C turns right.",
             f"L {s} (1010)^b 1 0 1 0 {q}> {w} R", f"L {s} (1010)^b 1 0 0 1 C> 1 R"),
        ]
RULES += [
    ("ret_z", "C over 1 0 1 (j = 0).", "L 1 C> 1 0 1 R", "L 0 1 0 1 C> R"),
    ("ret_o", "C over 1^(2j+1) 0 1, j = 2b+1.", "L 1 C> 1 1 1 (1111)^b 0 1 R", "L 1 (0101)^b 0 0 1 0 1 C> R"),
    ("ret_e", "C over 1^(2j+1) 0 1, j = 2b+2.", "L 1 C> 1 (1111)^b+1 0 1 R", "L 1 (0101)^b 0 1 0 0 1 0 1 C> R"),
    ("end_z", "C over 1 at the end (j = 0): the visit.", "L 1 C> 1 0^inf", "L 1 0 A> 0^inf"),
    ("end_o", "C over 1^(2j+1) at the end, j = 2b+1: the visit.", "L 1 C> 1 1 1 (1111)^b 0^inf",
     "L 1 (0101)^b 0 1 0 A> 0^inf"),
    ("end_e", "C over 1^(2j+1) at the end, j = 2b+2: the visit.", "L 1 C> 1 (1111)^b+1 0^inf",
     "L 1 (0101)^b+1 0 A> 0^inf"),
]


def scan(k, bl, ps):
    """Python mirror of `scan` in lean/Macro.lean (pairs (separator right of a counter, counter), nearest first)."""
    while True:
        if not ps:
            return None
        (s, c), rest = ps[0], ps[1:]
        v = bl[0] if bl else k
        back = [(False, p) for p in reversed(bl)]
        if v % 2 == 1:
            if s:
                return None if c == 0 else (k + 3, back + [(False, c - 1)] + rest)
            if not rest:
                return None
            bl, ps = [c] + bl, rest
            continue
        if s:
            if not bl:
                return (k + 2, [(False, c)] + rest)
            v, bl2 = bl[0], bl[1:]
            return None if v == 0 else (k + 3, [(False, p) for p in reversed(bl2)] + [(False, v - 1), (False, c)] + rest)
        return None if c == 0 else (k + 3, back + [(False, c - 1)] + rest)


def ordinary(k, ps):
    return None if k == 0 else scan(k, [], ps)


def to_pairs(cs, ss):
    return cs[-1], [(ss[i] == '1', cs[i]) for i in range(len(cs) - 2, -1, -1)]


def pairs_tape(k, ps):
    from counters import tape
    cs = [c for _, c in reversed(ps)] + [k]
    ss = ['1' if s else '0' for s, _ in reversed(ps)]
    return tape(cs, ss)


def check(N):
    """the mirror of `ordinary` against the machine itself on N random lists, and against counters.py on the first N
    visits from blank tape"""
    import random
    from counters import step, tape, machine_next
    rnd = random.Random(5)
    agree = none = 0
    for _ in range(N):
        m = rnd.randint(1, 7)
        cs = [rnd.randint(0, 6) for _ in range(m - 1)] + [rnd.randint(1, 9)]
        ss = [rnd.choice('01') for _ in range(m - 1)]
        r = ordinary(*to_pairs(cs, ss))
        if r is None:
            none += 1
            continue
        out, _ = machine_next(tape(cs, ss))
        assert out == pairs_tape(*r), (cs, ss, r, out)
        agree += 1
    cs, ss = [2, 2], ['0']; run = 0
    for _ in range(N):
        r = ordinary(*to_pairs(cs, ss))
        c2, s2, _, kind = step(cs, ss)
        assert (r is None) == (kind != 'ordinary'), (cs, ss, kind)
        if r is not None:
            assert pairs_tape(*r) == tape(c2, s2)
            run += 1
        cs, ss = c2, s2
    print('random lists: %d visits agree with the machine, %d none; run from blank: %d ordinary visits agree with '
          'counters.py, none exactly at the %d rebuilds' % (agree, none, run, N - run))


def main():
    if len(sys.argv) > 2 and sys.argv[1] == 'check':
        return check(int(float(sys.argv[2])))
    thms = []
    for name, doc, start, end in RULES:
        t, _ = prove(M, name, start, end, doc=doc, rotate=True, count_first=True, max_seg=60)
        thms.append(t)
    print(rules_file("Machine", NS, thms, "The local pieces of a visit (see lean/Macro.lean). Generated by `py/macro.py`."), end="")


if __name__ == "__main__":
    main()
