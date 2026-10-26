import sys, pickle, time
import ctl
from ctl import *
rounds = int(sys.argv[1]); ctl.KWIN = int(sys.argv[2]); ctl.CAP = int(sys.argv[3])
t0 = time.time()
P0, n = learn(rounds, cache=f"ctl_P_{rounds}_{ctl.KWIN}_{ctl.CAP}.pkl")
print("learned", len(P0), "windows from", n, "configurations", flush=True)
P, broken = saturate2(P0, log=lambda s: print(s, f"{time.time()-t0:.0f}s", flush=True))
pickle.dump((P0, P, ctl.PROV), open(f"ctl_sat_{rounds}_{ctl.KWIN}_{ctl.CAP}.pkl", "wb"))
print("P:", len(P0), "->", len(P))
if broken:
    print("UNFIXABLE:")
    for b in broken[:6]: print("  ", b)
else:
    D = DFA(Scanner(P)); print("final automaton", D.n)
    w = dispatch(D)
    print("dispatch:", "every configuration in INV matches a theorem" if w is None else "UNMATCHED " + w)
