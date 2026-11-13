"""Plain big-integer iteration of the E-pass map with the measured rules (rules.json, via emap.py), for checking
c/orbit.c: prints the final context, the bit length of n_K and n_K mod 2^64 after K passes from ('1', 19).
usage: python3 orbit_check.py K"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import emap  # noqa: E402

K = int(sys.argv[1])
c, n = "1", 19
for i in range(K):
    c, n = emap.step(c, n)
    if c == "HALT":
        print("HALT at pass", i)
        break
else:
    print(f"passes {K}: final context {c}; n_K bits {n.bit_length()}, n_K mod 2^64 = {n % 2**64}")
emap.save()
