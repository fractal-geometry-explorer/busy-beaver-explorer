"""The resets of 1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA at short tails, measured and closed up: start from the
tails that the level-2 resets leave (`x3`, `tl 0 y`, `s2` right after the d block) and from every nearly empty tail
of a suffix, run the plain machine from `0^inf B> 0 0 1 (1100)^n (10110110)^r T 0^inf` (n = 60..69) to the first
clean record (`c/firstrec.c`: m >= 1, or a tail starting 1001 or 101110, or the loop record `... 0 1`), and add what
the record leaves to the work list:

* a record (n', m', T) with T short: the phase end (T, m' mod 5) after the periods of the d block;
* a record whose tail is `10 (1110)^k S` with k growing with n: a long tail of suffix S, which the generic rows
  shorten until it is nearly empty: the tails `10 (1110)^t S`, t below what row r reads, for each r.

usage (from this folder):  gcc -O2 -o firstrec c/firstrec.c && python3 py/closure_table.py > runs/closure_table.txt
"""
import re
import subprocess
import sys

NEED = [4, 1, 4, 3, 2]
NS = range(60, 70)
KNOWN = {"01": "s0", "1001": "t1001", "1": "s1", "1001101011001": "s2", "11001011001": "x3", "101101001": "y"}


def rec(n, r, T):
    o = subprocess.run(["./firstrec", str(n), str(r), T, "1", "300000000", "1"], capture_output=True,
                       text=True).stdout.split()
    if o[0] in ("HALT", "TIMEOUT", "OUT"):
        return (o[0], int(o[1]) if len(o) > 1 else None)
    return ("rec", int(o[0]), int(o[1]), int(o[2]), o[3] if len(o) > 3 else "")


def split_tail(T):
    m = re.match(r"^10((?:1110)*)(.*)$", T)
    return (len(m.group(1)) // 4, m.group(2)) if m else (None, T)


def fit(xs):
    """xs over n = 60..69: 'n+k', a constant, 'floor((n+c)/2)' or None."""
    d = [x - n for x, n in zip(xs, NS)]
    if len(set(d)) == 1:
        return f"n{d[0]:+d}"
    if len(set(xs)) == 1:
        return str(xs[0])
    for c in range(-40, 60):
        if all(x == (n + c) // 2 for x, n in zip(xs, NS)):
            return f"floor((n{c:+d})/2)"
    return "?" + ",".join(map(str, xs))


def main():
    todo = [("11001011001", r) for r in range(5)] + [("101101001", r) for r in range(5)] + \
           [("1001101011001", r) for r in range(5)]
    seen, suffixes = set(), {"01", "1", "1001101011001"}
    out = []
    while todo:
        X, r = todo.pop(0)
        if (X, r) in seen:
            continue
        seen.add((X, r))
        if len(seen) > 200:
            print("too many states", file=sys.stderr)
            break
        rs = [rec(n, r, X) for n in NS]
        kinds = {x[0] for x in rs}
        line = f"T = {X} ({KNOWN.get(X, 'new')}), r = {r}: "
        if kinds == {"HALT"}:
            line += "HALT, steps " + fit([x[1] for x in rs])
        elif kinds != {"rec"}:
            line += "mixed " + " ".join(x[0] for x in rs)
        else:
            T = {x[4] for x in rs}
            ks = [split_tail(x[4]) for x in rs]
            n1, m1 = fit([x[1] for x in rs]), fit([x[2] for x in rs])
            if len(T) == 1:
                Tn = rs[0][4]
                if Tn == "01" and rs[0][2] == 0:
                    line += f"loop record, n' = {n1}"
                else:
                    line += f"(n', m') = ({n1}, {m1}), tail {Tn} ({KNOWN.get(Tn, 'new')})"
                    for m in {x[2] % 5 for x in rs}:
                        todo.append((Tn, m))
            elif len({s for _, s in ks}) == 1 and None not in [k for k, _ in ks]:
                S = ks[0][1]
                line += f"(n', m') = ({n1}, {m1}), long tail 10 (1110)^({fit([k for k, _ in ks])}) {S} " \
                        f"({KNOWN.get(S, 'new suffix')})"
                if S not in suffixes:
                    suffixes.add(S)
                    for rr in range(5):
                        for t in range(NEED[rr]):
                            todo.append(("10" + "1110" * t + S, rr))
            else:
                line += "varies: " + " | ".join(f"{x[1]} {x[2]} {x[4]}" for x in rs[:3])
        line += f"   [steps at n = 60: {rs[0][3] if rs[0][0] == 'rec' else rs[0][1]}]"
        print(line, flush=True)
    print(f"{len(seen)} states; suffixes {sorted(suffixes)}")


if __name__ == "__main__":
    main()
