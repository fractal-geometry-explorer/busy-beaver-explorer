"""Cycle coverage of 1RB0LD_1RC---_0RD0RE_1LE0RF_0LA0LD_1RD0RB: run the macro simulator with the cycle accelerator (bbtools.cycles, block size K),
and report which cycle shapes it proves and jumps over, and what fraction of the steps lies inside the jumps.
The shapes found are the ones proved for every surrounding tape in lean/Rules.lean (py/gen_rules.py).

usage (from the repository root): python3 holdouts/1RB0LD_1RC---_0RD0RE_1LE0RF_0LA0LD_1RD0RB/py/coverage.py STEPS
"""
import collections, os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "tools", "py"))
from bbtools.cycles import Accelerator
from bbtools.macro import MacroRun

M = "1RB0LD_1RC---_0RD0RE_1LE0RF_0LA0LD_1RD0RB"
K = 2


def main(steps):
    a = Accelerator(MacroRun(M, K)).run(steps)
    shapes, cycles, inside = collections.Counter(), collections.Counter(), 0
    by_name = {r.name: r for r in a.rules}
    for before, n, after, name in a.jumps:
        doc = [l for l in by_name[name].lean.split("\n") if l.startswith("/--")][0]
        sig = re.sub(r"\^n\d+", "^n", doc[len("/-- one cycle: "):-3])
        shapes[sig] += 1
        cycles[sig] += n
        inside += after - before
    r = a.run_
    print(f"{r.steps} steps, {len(a.rules)} cycle rules proved, {len(a.jumps)} jumps; "
          f"{inside / r.steps:.4f} of the steps inside jumps")
    for sig in shapes:
        print(f"  {shapes[sig]} jumps, {cycles[sig]} cycles: {sig}")


if __name__ == "__main__":
    main(float(sys.argv[1]))
