import json, sys, time
from fractions import Fraction as Fr
import ruleb as B
K, Emax = int(sys.argv[1]), int(sys.argv[2])
table = {}
for k in range(0, K + 1):
    t0 = time.time()
    leaves = B.explore(k, Emax)
    fixed = [(E, rho, [str(x) for x in r[1]], r[2]) for E, rho, r in leaves if r[0] == "fixed"]
    share_fixed = sum(Fr(1, 2 ** E) for E, rho, r in leaves if r[0] == "fixed")
    share_open = sum(Fr(1, 2 ** E) for E, rho, r in leaves if r[0] == "bit")
    consts = sorted({int(Fr(r[1][1])) for E, rho, r in leaves if r[0] == "fixed"})
    slopes = sorted({str(r[1][0]) for E, rho, r in leaves if r[0] == "fixed"})
    table[k] = dict(fixed=fixed, share_fixed=float(share_fixed), share_open=float(share_open),
                    maxE=max(E for E, _, _ in leaves), leaves=len(leaves))
    print(f"k={k:2d}: {len(fixed):4d} fixed classes, share of n* {float(share_fixed):.4f}, unresolved {float(share_open):.4f}, "
          f"digits needed up to {table[k]['maxE']}, jump = n* + {consts}  (slopes {slopes})  [{time.time()-t0:.0f}s]", flush=True)
    json.dump(table, open(f"ruleb_table_{K}_{Emax}.json", "w"))
