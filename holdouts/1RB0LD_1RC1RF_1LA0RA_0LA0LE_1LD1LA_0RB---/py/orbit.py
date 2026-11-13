"""The macro orbit of 1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---:
(3k, y) -> (4k+1, y+4), (3k+1, y) -> (4k+5, y+6), (3k+2, y) -> (4k+8, y-1), from (0, 0).
usage: python3 orbit.py N   (N macro steps; prints at powers of two: y, the size of z, the counts of the three
residues, y - 3n, and the smallest y over macro steps 1..n)."""
import sys, math
N = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10**5
z, y = 0, 0
cnt = [0, 0, 0]
miny_after = {}
miny, at = 10**9, None
for n in range(N):
    k, r = divmod(z, 3)
    cnt[r] += 1
    if n and y < miny: miny, at = y, n
    if r == 0:
        z, y = 4 * k + 1, y + 4
    elif y == 0:
        print("EXIT at macro step", n, "z mod 3 =", r); break
    elif r == 1:
        z, y = 4 * k + 5, y + 6
    else:
        z, y = 4 * k + 8, y - 1
    if n and (n & (n - 1)) == 0 or n == N - 1:
        lz = z.bit_length() * math.log10(2)
        print(f"n={n+1} y={y} z~10^{lz:.0f} residues={cnt} y-3n={y-3*(n+1)} min y (n>=1)={miny} at n={at}", flush=True)
