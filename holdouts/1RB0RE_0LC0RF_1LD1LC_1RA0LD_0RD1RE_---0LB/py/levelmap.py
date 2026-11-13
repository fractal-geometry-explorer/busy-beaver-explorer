"""The level map of 1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB for the four short tails, checked against the Lean rules.

A level starts at  0^inf D> 0 0 1^5 100 (10111)^b T 0^inf .  For T in {P, Q, R, S} and each b in a range this script
runs the machine itself (plain simulation, every step) to the start of the next level, and checks

 * that every visit of the left end on the way is an instance of one of the rules that `py/rules.py` proves in Lean
   (`grow`, the `enter*`, `drain*`, `end*`, `pourS*`, `endS*` rules): the start pattern of the rule matches the tape
   with all variables >= 0 and the end pattern, with the same values, is the tape at the next visit;
 * the closed formula for the next level (b', T').

usage (from the repo root): python3 holdouts/1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB/py/levelmap.py [BMIN BMAX]
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rules as RU  # noqa: E402

TAILS = {"P": RU.P, "Q": RU.Q, "R": RU.R, "S": RU.S}


def pattern(s):
    """Rule side -> (regex, list of (group name, variable, offset)); the tape is the cells from the head on."""
    body = s.split("D>")[1].split()
    ctx = body[-1] != "0^inf"
    body = body[:-1]
    rx, groups = "", []
    for i, t in enumerate(body):
        m = re.fullmatch(r"\((\d+)\)\^(.+)", t)
        if not m:
            rx += t
            continue
        w, e = m.group(1), m.group(2)
        if e.isdigit():
            rx += w * int(e)
            continue
        v, _, k = e.partition("+")
        g = f"g{i}"
        rx += f"(?P<{g}>(?:{w})*)" + w * int(k or 0)
        groups.append((g, v, len(w)))
    return re.compile(rx + ("(?P<R>.*)" if ctx else "0*") + "$"), groups


def instantiate(s, env, R=""):
    body = s.split("D>")[1].split()[:-1]
    out = ""
    for t in body:
        m = re.fullmatch(r"\((\d+)\)\^(.+)", t)
        if not m:
            out += t
        else:
            v, _, k = m.group(2).partition("+")
            n = int(v) if v.isdigit() else env[v] + int(k or 0)
            out += m.group(1) * n
    return (out + R).rstrip("0")


def find_rule(infos, tape, nxt):
    for i in infos:
        rx, groups = i["_pat"]
        m = rx.match(tape)
        if not m:
            continue
        env, ok = {}, True
        for g, v, L in groups:
            n = len(m.group(g)) // L
            if env.setdefault(v, n) != n:
                ok = False
        # a variable in two blocks (grow): retry with the smaller value if the greedy split disagrees
        if not ok:
            continue
        R = m.groupdict().get("R") or ""
        if instantiate(i["end"], env, R) == nxt:
            return i["name"], env
    return None


def tape_of(a, X):
    return ("0011111" + "00111" * a + X).rstrip("0")


def level(b, T, infos):
    """Run one level; returns (b', T', visits, names of the rules used)."""
    a, X, used, visits = 0, "100" + "10111" * b + T, [], 0
    while True:
        a2, X2, _ = RU.visit(a, X)
        r = find_rule(infos, tape_of(a, X), tape_of(a2, X2))
        if r is None:
            raise SystemExit(f"no rule for the visit at a={a} X={X[:80]} (b={b})")
        used.append(r[0])
        visits += 1
        if a2 < a:
            m = re.match(r"100((?:10111)*)(.*)$", X2)
            return len(m.group(1)) // 5, m.group(2), visits, used
        a, X = a2, X2


def name_tail(t):
    for k, v in TAILS.items():
        if t == v:
            return k
    m = re.fullmatch(r"10011111000111((?:001)+)10011110011110111110111", t)
    if m:
        return f"100 1^5 000 111 (001)^{len(m.group(1)) // 3} 100 1111 00 1111 0 1^5 0 111"
    m = re.fullmatch(r"((?:100111)+)", t)
    if m:
        return f"(100111)^{len(t) // 6}"
    m = re.fullmatch(r"10011111((?:001111)+)0111", t)
    if m:
        return f"100 1^5 (001111)^{len(m.group(1)) // 6} 0 111"
    return t


FORMULA = {  # tail -> b mod 4 -> (numerator coefficients (p, q): b' = (p*b + q) / 2, next tail)
    "P": {0: (9, 10, "P"), 1: (9, 11, "Q"), 2: (9, 10, "R"), 3: (9, 9, "S")},
    "Q": {0: (9, 12, "P"), 1: (9, 13, "Q"), 2: (9, 12, "R"), 3: (9, 11, "S")},
    "R": {r: (2, 8, None) for r in range(4)},
    "S": {0: (4, 6, None), 1: (4, 8, None), 2: (4, 6, None), 3: (4, 8, None)},
}


def main():
    lo, hi = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (12, 28)
    hand, visits = RU.build()
    infos = [i for _, i in hand + visits]
    for i in infos:
        i["_pat"] = pattern(i["start"])
    allused = set()
    bad = 0
    for T in "PQRS":
        for b in range(lo, hi):
            b2, t2, n, used = level(b, TAILS[T], infos)
            allused |= set(used)
            p, q, nt = FORMULA[T][b % 4]
            ok = 2 * b2 == p * b + q and (nt is None or t2 == TAILS[nt])
            bad += not ok
            print(f"{T} b={b:3} -> b'={b2:4} tail {name_tail(t2)}   {n} visits, all instances of Lean rules; formula {'ok' if ok else 'WRONG'}")
    print(f"rules used: {len(allused)} of {len(infos)}; unused: {sorted(set(i['name'] for i in infos) - allused)}")
    print("ALL OK" if not bad else f"{bad} formula mismatches")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
