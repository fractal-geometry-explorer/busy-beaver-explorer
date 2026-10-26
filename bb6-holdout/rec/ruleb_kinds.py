"""Split the Rule B table: is offset k itself a virtual clean round (the virtual tape just finished a cycle, so this is
Rule A one level down), or does the class close in the middle of a virtual cycle?"""
import json
from fractions import Fraction as Fr
import ruleb as B
tab = json.load(open("ruleb_table_20_22.json"))
def state_after(k, E, rho, rounds):
    ctx = B.Ctx(E, rho)
    w = B.P(2, 0, 2, 5); marks = [["G", B.P(0, 0, 0, 1)], ["M", B.P(0, 2 ** (k + 1))], ["M", B.P(2, 0, 2, 3)]]
    for r in range(rounds): w, marks = B.round_events(ctx, w, marks)
    return marks
print(" k   fixed share   at a virtual clean tape   mid-cycle")
for k in sorted(tab, key=int):
    k_ = int(k); a = b = Fr(0)
    for E, rho, jump, rds in tab[k]["fixed"]:
        ms = state_after(k_, E, rho, k_)
        clean = len(ms) == 3 and ms[1][0] == "M" and ms[1][1].v[0] == 0 and ms[2][0] == "M" and ms[2][1].v[0] == 2
        if clean: a += Fr(1, 2 ** E)
        else: b += Fr(1, 2 ** E)
    print(f"{k_:2d}   {float(a+b):.4f}        {float(a):.4f}                    {float(b):.4f}")
