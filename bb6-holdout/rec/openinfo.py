import sys, collections
import nrefine as NR
K = int(sys.argv[1])
_, settled, open_ = NR.refine(K)
open_ = sorted({rho % 2 ** K for k, rho in open_})
def v2(x):
    c = 0
    while x % 2 == 0 and c < 99: x //= 2; c += 1
    return c
# where does each open class need its next digit?  record the round of the pending test
orig = NR.mod4; info = {}
def run(rho):
    rd = [0]
    def m4(d):
        if d[0] % 4: raise NR.NeedBit(rd[0])
        return d[1] % 4
    NR.mod4 = m4
    try: NR.cycle(K, rho)
    except NR.NeedBit as e: return e.args
    finally: NR.mod4 = orig
byv = collections.Counter(min(v2(r + 2), 12) for r in open_)
print(f"{len(open_)} classes open at {K} digits;  by trailing zeros of n+2:", dict(sorted(byv.items())))
print("share with n+2 having >= 4 trailing zeros:", round(sum(c for v, c in byv.items() if v >= 4) / len(open_), 3),
      "  (all n: 0.0625)")
