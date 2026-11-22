"""Round map of the closed counter model coq/SOC23Model.v, for
1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB--- and 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1RC---.

A round starts at cfgL L 0 X (left counter of L digits at 0, right counter X) and ends at the next one.
round(L, X) follows the model step f of SOC23Model.v, jumping over each countdown at once:
  cfgS? len k h n m  (n > 0)  ->  cfgS? len (k-n) h 0 m        (n pairs RS?_Inc, LC_Inc)
  cfgR  len k n               ->  cfgL len 0 (n+k+1)           (k+1 pairs RC_Inc, LC_Inc)
It returns None at a corner X = 2^L, the only configuration f has no successor for.
SOC23_Holdouts.v proves that both machines reach cfgL 2 0 5 and that a halt needs a corner.

usage: python3 model23.py ROUNDS        (iterate from (2, 5), report every 1000 rounds)
"""
import sys
sys.set_int_max_str_digits(0)


def split(m):
    """m = (x*2+1)*2^i -> (x, i), m > 0."""
    i = (m & -m).bit_length() - 1
    return m >> (i + 1), i


def round_map(L, X):
    if X == 2 ** L:
        return None                                   # corner
    m, i = split(X)                                   # LC_Ov
    st = ('S0', L, 2 ** L - 1, i, (2 ** i - 1) * 2, m)
    while True:
        if st[0] == 'R':
            _, ln, k, n = st
            return ln, n + k + 1                      # countdown to the next round start
        kind, ln, k, h, n, m = st
        if n > 0:
            assert n <= k                             # the invariant P
            st = (kind, ln, k - n, h, 0, m)
            continue
        a = h // 2
        def app(j, plus1=False):
            return ln + 1 + j, (2 * k + 1) * 2 ** j - (0 if plus1 else 1)
        if kind == 'S0':
            if h % 2 == 0:                            # RS0_Ov_0 (rule R1)
                L2, K2 = app(3 * a)
                if m == 0:
                    st = ('R', L2, K2, 1)
                else:
                    x, i2 = split(m); st = ('S1', L2, K2, i2, (2 ** i2 - 1) * 2, x)
            else:                                     # RS0_Ov_1 (rule R2)
                L2, K2 = app(3 * a + 2)
                if m == 0:
                    st = ('R', L2, K2, 0)
                else:
                    x, i2 = split(m); st = ('S0', L2, K2, i2, (2 ** i2 - 1) * 2 + 1, x)
        else:
            if h % 2 == 0:
                if m == 0:                            # RS1_Ov_0_blank (rule R3)
                    L2, K2 = app(3 * a + 2); st = ('R', L2, K2, 0)
                elif m % 2 == 0:                      # RS1_Ov_0_even (rule R3)
                    L2, K2 = app(3 * a + 2)
                    x, i2 = split(m // 2); st = ('S1', L2, K2, i2, (2 ** i2 - 1) * 2 + 1, x)
                else:                                 # RS1_Ov_0_odd (rule R4)
                    L2, K2 = app(3 * a + 1)
                    x, j = split(m + 1); st = ('S0', L2, K2, j, (2 ** j - 1) * 2, x)
            else:                                     # RS1_Ov_1 (rule R5)
                L2, K2 = app(3 * a + 3, plus1=True); st = ('R', L2, K2, m)


if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    L, X = 2, 5
    closest = None
    for t in range(N):
        r = round_map(L, X)
        if r is None:
            print('corner at round', t, 'L =', L); break
        L, X = r
        d = abs(2 ** L - X).bit_length()
        if t > 3:
            closest = d / L if closest is None else min(closest, d / L)
        if t % 1000 == 0 or t == N - 1:
            print(f'round {t}: L = {L}, |X - 2^L| has {d} bits, smallest ratio bits/L since round 4: {closest}', flush=True)
