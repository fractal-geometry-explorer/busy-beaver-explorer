"""Symbolic search over the parity patterns of the blocks a sweep meets (bbtools.symtm with every count a variable):
prints, for each pattern of up to K inner blocks that ends the sweep without looking further left, the change of the
counts (last block first) and the step count.  python3 holdouts/<M>/py/patterns.py [K=6]"""
import itertools, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gen_rules import start, run_to_end   # noqa: E402  (also rewrites nothing: gen_rules only writes when run as main)
from bbtools import symtm                  # noqa: E402
from bbtools.symtm import Rep, Blank, Ctx  # noqa: E402


def cells(toks, env):
    out = []
    for t in toks:
        if isinstance(t, int):
            out.append(t)
        elif isinstance(t, Rep):
            out += list(t.word) * t.n.subs(env)
    return out


K = int(sys.argv[1]) if len(sys.argv) > 1 else 6
done = set()
for k in range(1, K + 1):
    for inner in itertools.product("EO", repeat=k):
        for last in "EO":
            key = last + "|" + "".join(inner)
            if any(key[:len(key) - j] in done for j in range(1, k)):
                continue
            try:
                fin = run_to_end(start(last, "".join(inner)))
            except symtm.TouchContext:
                continue
            done.add(key)
            env = {f"y{i + 1}": 3 + i for i in range(k)}
            env["c"] = 5
            before = [2 * 5 + (6 if last == "E" else 5)] + [2 * env[f"y{i + 1}"] + (4 if p == "E" else 5)
                                                             for i, p in enumerate(inner)]
            tape = "".join(map(str, cells(fin.left + fin.right, env))).strip("0")
            groups = [g.count("1") for g in tape.split("00")][::-1]   # last block first
            change = [a - b for a, b in zip(groups, before)]
            print(key, change, fin.steps)
