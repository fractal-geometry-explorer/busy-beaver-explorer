"""The E-pass map of 1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---.

An E-event is the head, in state E, entering from the left the last run of 1s of the tape (`c E> 1^n`, blank beyond),
with the word `c` (from the first 1 of the tape up to the head) the *context*.  From blank tape the first is
c = '1', n = 19 at step 153.  One E-pass converts 1^n into (10)^(n/2), a loop at the right end turns the 10s back
into a longer run of 1s, and B-passes eat the context from the right; the next E-event is (c', n') with

    n' = (3n + delta) / 2,   (c', delta) depending only on c and n mod 4

(and c' only on c and on the bit b = ceil(n/2) mod 2).  The rules are found by direct simulation of `c E> 1^n` for two
values of n in each class (c/epass.c) and cached in rules.json.  Some contexts halt (e.g. '11111' with b = 1).

usage: python3 emap.py rule CTX               the four rules of a context
       python3 emap.py blank STEPS            the E-events of the blank run (c/enter.c), checked against the rules
       python3 emap.py orbit N                N E-passes from blank (big integers)
       python3 emap.py markov STEPS           halting rate per E-pass if b is a fair coin (distribution propagation)
       python3 emap.py path                   the shortest bit sequence from context '1' to a halt
"""
import json, os, subprocess, sys
from collections import Counter, deque

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import g01tools as g  # noqa: E402

M = "1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---"
RF = os.path.join(HERE, "rules.json")
rules = json.load(open(RF)) if os.path.exists(RF) else {}
dirty = False


def epass(c, n, N=400000000):
    return subprocess.run([g.binary("epass"), M, c, str(n), str(N), str(n // 3)], capture_output=True,
                          text=True).stdout.split()


def rule(c, r):
    """[c', delta] for context c and n = r mod 4, or ['HALT', t1, t2]"""
    global dirty
    k = f"{c},{r}"
    if k not in rules:
        base = max(200, 40 * len(c))
        n1, n2 = base + r, 2 * base + 4 + r
        o1, o2 = epass(c, n1), epass(c, n2)
        if o1[0] == "HALT":
            assert o2[0] == "HALT"
            rules[k] = ["HALT", int(o1[1]), int(o2[1])]
        else:
            d1, d2 = 2 * int(o1[1]) - 3 * n1, 2 * int(o2[1]) - 3 * n2
            assert o1[0] == o2[0] and d1 == d2, (c, r, o1, o2)
            rules[k] = [o1[0], d1]
        dirty = True
    return rules[k]


def save():
    if dirty:
        json.dump(dict(sorted(rules.items())), open(RF, "w"), indent=0)


def step(c, n):
    c2, d = rule(c, n % 4)[:2]
    return (c2, None) if c2 == "HALT" else (c2, (3 * n + d) // 2)


if __name__ == "__main__":
    cmd = sys.argv[1]
    try:
        if cmd == "rule":
            for r in range(4):
                print(sys.argv[2], "n = %d mod 4:" % r, rule(sys.argv[2], r))
        elif cmd == "blank":
            p = subprocess.Popen([g.binary("enter"), M, str(int(float(sys.argv[2]))), "10", "400"],
                                 stdout=subprocess.PIPE, text=True)
            prev, ok = None, 0
            for line in p.stdout:
                f = line.split()
                if len(f) < 5 or f[1] != "E":
                    continue
                c, n = f[2], int(f[4])
                if prev:
                    assert step(*prev) == (c, n), (prev, c, n)
                    ok += 1
                prev = (c, n)
                print(f[0], c, n)
            print(f"blank: {ok} consecutive E-events follow the rules")
        elif cmd == "orbit":
            c, n = "1", 19
            cnt = Counter()
            N = int(sys.argv[2])
            for i in range(N):
                cnt[c] += 1
                c, n = step(c, n)
                if c == "HALT":
                    print("HALT after", i + 1, "E-passes")
                    break
            print(f"orbit: {i + 1} E-passes from blank, no halt; n has {int(n.bit_length() * 0.30103) + 1} digits;"
                  f" {len(cnt)} contexts used, longest {max(map(len, cnt))}")
            print(" ".join(f"{c}:{k}" for c, k in cnt.most_common()))
        elif cmd == "markov":
            P, H = {"1": 1.0}, 0.0
            for t in range(int(sys.argv[2])):
                Q, h = {}, 0.0
                for c, p in P.items():
                    for r in range(4):
                        c2 = rule(c, r)[0]
                        if c2 == "HALT":
                            h += p / 4
                        else:
                            Q[c2] = Q.get(c2, 0) + p / 4
                P = {c: p for c, p in Q.items() if p >= 1e-26}
                H += h
            print(f"markov: {len(P)} contexts carry the mass; halting probability per E-pass {h:.4e}"
                  f" (mean {1 / h:.3e} E-passes to a halt); total after {t + 1} passes {H:.3e}")
        elif cmd == "path":
            prev, q, found = {"1": None}, deque(["1"]), None
            while q and not found:
                c = q.popleft()
                for b, r in ((0, 3), (1, 1)):
                    c2 = rule(c, r)[0]
                    if c2 == "HALT":
                        found = (c, b)
                        break
                    if c2 not in prev:
                        prev[c2] = (c, b)
                        q.append(c2)
            path = [found]
            while prev[path[-1][0]]:
                path.append(prev[path[-1][0]])
            path.reverse()
            print(f"path: {len(path)} E-passes; bits " + "".join(str(b) for _, b in path))
            print(" -> ".join(c for c, _ in path) + " -> HALT")
    finally:
        save()
