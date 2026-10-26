"""States near each plateau pattern's limit geometry (fixed point as fractions of the width), with random low digits,
for runshape F: what loop entries follow a plateau."""
import json, random, sys
LEN = {'G': 3, 'M': 2, 'W': 2, 'B': 3}; VAL = {'G': 0, 'M': 1, 'W': 0, 'B': 1}
def valid(W, ms):
    f = ms[0]
    if f[1] == 0:
        if VAL[f[0]] == 0: return False
    elif (f[1] % 2 == 1) != (VAL[f[0]] == 0): return False
    for a, b in zip(ms, ms[1:]):
        L = b[1] - (a[1] + LEN[a[0]] - 1) - 1
        if L < 0: return False
        if L == 0 and VAL[a[0]] == VAL[b[0]]: return False
        if L > 0 and ((L % 2 == 1) != (VAL[a[0]] == VAL[b[0]])): return False
    l = ms[-1]; T = W - 1 - (l[1] + LEN[l[0]] - 1)
    if T < 0: return False
    if T == 0: return VAL[l[0]] == 1
    return (T % 2 == 1) == (VAL[l[0]] == 0)
d = json.load(open('patinst.json'))
N = int(sys.argv[1]); random.seed(int(sys.argv[2]))
out = open(sys.argv[3], 'w'); keys = []
for key, (Ws, marks, fstar) in d.items():
    if fstar is None: continue
    W0 = int(Ws); ms0 = [(t, int(p)) for t, p in marks]
    endm = ms0[-1][0] == 'M' and ms0[-1][1] == W0 - 2
    inner = fstar[:len(fstar) - (1 if endm else 0)]
    if inner and max(inner) > 1 - 1e-9: continue          # a progress pattern, not a plateau
    made = 0; tries = 0
    while made < N and tries < 50 * N:
        tries += 1
        W = random.randrange(1 << 61, 1 << 62)
        if (W - W0) % 2: W += 1
        ms = [('G', 1)]
        for i, (t, p0) in enumerate(ms0[1:]):
            if endm and i == len(ms0) - 2: p = W - 2
            else:
                p = int(fstar[i] * W) + random.randrange(-(W >> 22), W >> 22)
                if (p - p0) % 2: p += 1
            ms.append((t, p))
        if any(b[1] <= a[1] for a, b in zip(ms, ms[1:])) or not valid(W, ms): continue
        out.write(str(W) + ' ' + ' '.join(t + ' ' + str(p) for t, p in ms) + '\n'); made += 1
    keys.append((key, made))
print(len(keys), 'plateau patterns,', sum(m for _, m in keys), 'states')
