import random
from conc import Model
def v2(x):
    if x == 0: return 999
    c = 0
    while x % 2 == 0: x //= 2; c += 1
    return c
CYC = ['GBW', 'GMB', 'GMWW', 'GMB', 'GMWW', 'GWWW', 'GBW', 'GWWW']
def cycles(a, b, c, E, maxc=40):
    m = Model(1); m.W = m.const(E); m.add('G', m.const(1))
    for v in (a, b, c): m.add('W', m.const(v))
    k = 0
    while k < maxc:
        for want in CYC:
            m.do_round()
            if m.bad or m.halted or m.shape() != want: return k
        k += 1
    return k
# random 4D states near the sample geometry, with planted fuels
random.seed(3); stats = {}
base = [1559396385, 6743276446, 10381864607, 10395969088]
SC = 2**120 // base[3]
for trial in range(4000):
    fR_t = random.randint(1, 30); fL_t = random.randint(1, 45)
    E = (base[3] * SC + random.getrandbits(60)) & ~((1 << 46) - 1)
    E += random.getrandbits(46) & ~3
    c = E - 1 - (1 << fR_t) * (2 * random.getrandbits(40) + 1)
    # b with 1029 b = 784 E + 1302 + 2^fL * odd  (mod 2^200)
    M = 2**200
    target = (784 * E + 1302 + (1 << fL_t) * (2 * random.getrandbits(40) + 1)) * pow(1029, -1, M) % M
    b0 = base[1] * SC; b = b0 - ((b0 - target) % (1 << 100))
    a = base[0] * SC | 1
    if not (a < b < c < E): continue
    fL = v2(1029 * b - 784 * (c + 1) - 1302); fR = v2(E - c - 1)
    pred = max(0, min((fL - 3) // 6, (fR - 1) // 4))
    act = cycles(a, b, c, E)
    key = (pred == act)
    stats[key] = stats.get(key, 0) + 1
    if pred != act and stats[False] <= 8: print("mismatch: fL", fL, "fR", fR, "pred", pred, "actual", act)
print(stats)
