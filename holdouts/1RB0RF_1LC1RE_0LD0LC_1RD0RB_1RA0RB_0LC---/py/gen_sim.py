"""Write lean/Sim.lean and lean/Bound.lean for one of the five sister machines of
1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC--- from the templates Sim.lean.in and Bound.lean.in in this folder.

Sim.lean completes the machine's partial macro map (`astep` of its Full.lean, made by gen_full.py) with a checked
direct simulation of the irregular steps (`tstep`), so that the run from blank tape reduces to one map `mstep`, as
for the 0LC machine.  Bound.lean runs that map K steps by compiled evaluation; NT is the number of simulated
stretches on the way (from `py/check_mstep.py count`).

usage (from the repository root):
  python3 holdouts/1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---/py/gen_sim.py MACHINE [K NT]
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def main():
    m = sys.argv[1]
    d = os.path.join(HERE, "../../", m, "lean")
    ns = re.search(r"^namespace (\w+)", open(os.path.join(d, "Machine.lean")).read(), re.M).group(1)
    sim = open(os.path.join(HERE, "Sim.lean.in")).read().replace("@@NS@@", ns).replace("@@M@@", m)
    open(os.path.join(d, "Sim.lean"), "w").write(sim)
    if len(sys.argv) > 3:
        k, nt = int(sys.argv[2]), sys.argv[3]
        ktxt = f"10^{len(str(k)) - 1}" if k == 10 ** (len(str(k)) - 1) else str(k)
        b = open(os.path.join(HERE, "Bound.lean.in")).read()
        for a, v in (("@@NS@@", ns), ("@@M@@", m), ("@@KTXT@@", ktxt), ("@@K@@", str(k)), ("@@NT@@", nt)):
            b = b.replace(a, v)
        open(os.path.join(d, "Bound.lean"), "w").write(b)


if __name__ == "__main__":
    main()
