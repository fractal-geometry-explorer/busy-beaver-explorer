import sys, pickle
import ctl
from ctl import *
rounds, K, C = map(int, sys.argv[1:4]); ctl.KWIN = K; ctl.CAP = C
P0, P, PROV = pickle.load(open(f"ctl_sat_{rounds}_{K}_{C}.pkl", "rb"))
def explain(text, depth=0, seen=set(), maxd=12):
    w = windows_of(text.replace("|", ""))
    for win in sorted(w - P0, key=str):
        if win in seen: continue
        seen.add(win)
        it, name, st, en = PROV[win]
        print("  " * depth + f"{show_window(win)}   <- it{it} {name}: {st}  ->  {en}")
        if depth < maxd: explain(st, depth + 1, seen)
explain(sys.argv[4])
