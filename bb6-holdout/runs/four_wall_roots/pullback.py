"""Pull a pass start (b, W, R) back through the loop chain's three step maps (BB6/Ends.lean StepMap/StepWall).
Returns predecessors (kind, E, R0, b0, a_landing) that are pass starts with every gap >= 448 (a0 free, >= 449)."""
def L1(b, W, R): return 147*b - 112*W + 392*R - 186
def preds(b, W, R):
    L = L1(b, W, R); out = []
    # full: W = E + 24, R = R0/16, L = L0/64
    E, R0, L0 = W - 24, 16*R, 64*L
    out.append(('full', E, R0, L0))
    # half: W = E + 6, 2R = R0, 2L = L0 + 35E - 147R0 - 60, E%4==2
    E = W - 6; R0 = 2*R; L0 = 2*L - 35*E + 147*R0 + 60
    if E % 4 == 2: out.append(('half', E, R0, L0))
    # break7: W = E + 24; 4704R = 476E + 980R0 - L0 + 15984; 96L = L0 + 1120E + 1666R0 + 50328
    E = W - 24; num = 4704*R - 1596*E + 96*L - 66312
    if num % 2646 == 0:
        R0 = num // 2646; L0 = 96*L - 1120*E - 1666*R0 - 50328
        out.append(('break7', E, R0, L0))
    res = []
    for k, E, R0, L0 in out:
        nb = L0 + 112*E - 392*R0 + 186
        if nb % 147: res.append((k, E, R0, None, 'b not integral')); continue
        b0 = nb // 147
        ok = R0 >= 2 and R0 % 2 == 0 and E % 2 == 0 and b0 % 2 == 0 and b0 >= 897 and b0 + 449 + R0 <= E
        # landing's first wall from StepWall
        if k == 'full': na, d = L0 + 2464*E - 980*R0 + 99264, 9408
        elif k == 'half': na, d = L0 + 112*E - 392*R0 + 1656, 294
        else: na, d = L0 + 406*E - 539*R0 + 19884, 2352
        a1 = na // d if na % d == 0 else None
        res.append((k, E, R0, b0, 'ok' if ok else 'not a pass start', a1))
    return res
def shape(b, W, R):
    D = W - b; s = []
    if W <= 32*R: s.append('entry/r7')
    if W <= 64*R + 6 and 2*D + 900 <= W + 2*R: s.append('half')
    if 15*W + 144*R + 375 <= 64*D and 64*D + 994 <= 16*W + 128*R: s.append('fullwin')
    return s
