"""The E-event after Z_k in the region n < 12k + 12 (and Z_0 for every n), read off the proved families of
lean/zreg.json (made by gen_zreg.py), and checked against direct simulation.

    python3 zmap.py check KMAX         every (k, n) of the region with k < KMAX against direct simulation
    python3 zmap.py sample N           N random (k, n) of the region with k < 300

`zstep(k, n)` returns ('halt',) for the halting family (k odd, n = 12k + 9), else (n', tail string)."""
import json
import os
import random
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CASES = json.load(open(os.path.join(HERE, "..", "lean", "zreg.json")))["cases"]
BY = {c["name"]: c for c in CASES}


def ev(expr, env):
    return eval(expr.replace("^", "**"), {}, dict(env))


def word(tail, env):
    out = ""
    for t in tail.split():
        m = re.fullmatch(r"\(([01]+)\)\^(.+)", t)
        out += m.group(1) * ev(m.group(2), env) if m else t
    return out


def gen_C(prefix):
    """C of the generic family `prefix` (from its k expression)"""
    c = BY[prefix]
    return int(c["k"].split("+")[-1])


def pick(k, n):
    """(case name, env) for the E-event after Z_k at n, or None outside the region"""
    if k == 0 and n >= 24:
        return f"zz{n % 2}", {"m": (n - 24) // 2}
    if not (n < 12 * k + 12 or k == 0):
        return None
    if n < 24:
        r = n
        q = 8 if r % 8 == 7 else 1
        name = f"zs{r}_{k % q}" if q > 1 else f"zs{r}"
        C = gen_C(name)
        if k >= C:
            return name, {"e": (k - C) // q}
        return ("zh0" if (r, k) == (21, 1) else f"zt{r}_{k}"), {}
    j, r = (n - 24) // 24, (n - 24) % 24
    s = k - 2 * j
    q = 8 if r % 8 == 7 else 1
    name = f"zr{r}_{s % q}" if q > 1 else f"zr{r}"
    C = gen_C(name)
    if s >= C:
        return name, {"j": j, "e": (s - C) // q}
    return ("zh" if (r, s) == (21, 3) else f"zb{r}_{s}"), {"j": j}


def zstep(k, n):
    p = pick(k, n)
    if p is None:
        return None
    name, env = p
    c = BY[name]
    assert ev(c["n"], env) == n and ev(c["k"], env) == k, (name, env, k, n)
    if c["kind"] == "halt":
        return ("halt",)
    return ev(c["n2"], env), word(c["tail2"], env)


def check(k, n, sim):
    z = zstep(k, n)
    d = sim(n, k)
    if z == ("halt",):
        return d == "HALT"
    return d is not None and d != "HALT" and (d[1], d[0]) == z


if __name__ == "__main__":
    import gen_zreg as G
    if sys.argv[1] == "check":
        K = int(sys.argv[2])
        bad = cnt = 0
        for k in range(K):
            for n in range(0, max(12 * k + 12, 60 if k == 0 else 0)):
                cnt += 1
                if not check(k, n, G.sim):
                    bad += 1
                    print("MISMATCH", k, n, zstep(k, n), G.sim(n, k), flush=True)
        print(f"check: {cnt} starts with k < {K}, {bad} mismatches")
    elif sys.argv[1] == "sample":
        random.seed(1)
        bad = 0
        N = int(sys.argv[2])
        for _ in range(N):
            k = random.randrange(0, 300)
            n = random.randrange(0, 12 * k + 12)
            if not check(k, n, G.sim):
                bad += 1
                print("MISMATCH", k, n, flush=True)
        print(f"sample: {N} random starts with k < 300, {bad} mismatches")
