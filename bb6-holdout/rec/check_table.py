import json, random
from fractions import Fraction as Fr
import ruleb as B
tab = json.load(open("ruleb_table_20_22.json"))
class Concrete(B.Ctx):
    def __init__(s): pass
    def mod4(s, d): assert d.v[0] == d.v[1] == d.v[2] == 0 and d.v[3].denominator == 1; return int(d.v[3]) % 4
def concrete_jump(k, v, m, ns):
    ctx = Concrete(); N = (m << v); C = lambda x: B.P(0, 0, 0, x)
    w = C(2 * N + 2 * ns + 5); marks = [["G", C(1)], ["M", C(m << (k + 1))], ["M", C(2 * N + 2 * ns + 3)]]
    for r in range(1, 400):
        w, marks = B.round_events(ctx, w, marks)
        if len(marks) == 2 and marks[1][0] == "M" and marks[1][1] == w - 2: return (int(w.v[3]) - (2 * N + 2)) // 2
    return None
random.seed(7); bad = checked = varied = 0
for k in sorted(tab, key=int):
    fixed = tab[k]["fixed"]
    for _ in range(150):
        ns = random.getrandbits(24) * 3 + 1                      # virtual tapes are 1 mod 3
        hit = [f for f in fixed if ns % 2 ** f[0] == f[1]]
        js = {concrete_jump(int(k), int(k) + 50, random.getrandbits(40) | 1, ns) for _ in range(3)}
        checked += 1
        if hit:
            pred = ns + int(Fr(hit[0][2][1]))
            if js != {pred}: bad += 1; print("MISMATCH k", k, ns, js, pred)
        elif len(js) > 1: varied += 1
print(f"{checked} random (k, n*) cases, 3 random m each: table-fixed cases all match: {bad == 0}; "
      f"of the cases the table calls not fixed, {varied} already showed different jumps with just 3 values of m")
