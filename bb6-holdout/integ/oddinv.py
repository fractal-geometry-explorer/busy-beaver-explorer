# Common affine eigenforms F = a*m + b*E + c (mod p) of the eight largest return pieces of two-marker states
# (../lock/LOCK_NOTES.md, section 7): F(piece(m, E)) = lambda_i * F(m, E) (mod p) for every piece i.  A conserved
# quantity mod an odd p of this kind is what a 2-adic class cannot see.
# usage: python3 oddinv.py [bound]   (output: oddinv.out)
import sys

# D*m' = u*m + B*E + C, E' = E + e
PIECES = [(4, 1, 0, 0, 6), (8, 1, 6, 18, 12), (8, 1, 0, 0, 12), (16, 1, 6, 94, 18), (8, 1, 1, 27, 18),
          (16, 1, 2, 26, 18), (32, 1, 30, 438, 24), (16, 1, 13, 199, 24)]

def odd_primes(n):
    s = [True] * (n + 1)
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            for j in range(i * i, n + 1, i):
                s[j] = False
    return [i for i in range(3, n + 1) if s[i]]

def eigenforms(p):
    found = []
    # projective representatives of (a, b, c)
    cands = [(1, b, c) for b in range(p) for c in range(p)] + [(0, 1, c) for c in range(p)] + [(0, 0, 1)]
    for v in cands:
        ok = True
        for (D, u, B, C, e) in PIECES:
            iD = pow(D, -1, p)
            a, b, c = v
            w = (a * u * iD % p, (a * B * iD + b) % p, (a * C * iD + b * e + c) % p)
            k = next(i for i in range(3) if v[i] % p)
            lam = w[k] * pow(v[k], -1, p) % p
            if any((w[i] - lam * v[i]) % p for i in range(3)):
                ok = False
                break
        if ok:
            found.append(v)
    return found

bound = int(sys.argv[1]) if len(sys.argv) > 1 else 400
print(f"odd primes p < {bound}: common affine eigenforms (a, b, c) of the eight pieces other than constants")
for p in odd_primes(bound):
    f = [v for v in eigenforms(p) if v != (0, 0, 1)]
    if f:
        print(f"  p = {p}: {f}")
print("for every other odd prime below the bound: constants only")
