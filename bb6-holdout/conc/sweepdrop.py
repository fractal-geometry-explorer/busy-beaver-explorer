"""Three-number family (four-wall tapes with 11c - 5E fixed): for each width exponent K, the word P^a U L^b with a
plain stretch of about the lock's size minus 2 passes, final end distance pinned to a small odd value; run the real
machine (through the proven rules) on the nearest point of the lattice."""
import sys, math
import mixdrop
for K in map(int, sys.argv[1:]):
    b = int((K + 5.5) / 6) - 2
    # total halvings: 4a (P passes) + 3 (U) + 4b (plain) = K - 3.64 - log2(Rend - 1); aim at Rend - 1 about 2 to 6
    for a in sorted({max(1, int(round((K - 3.64 - 3 - 4 * b - 1.5) / 4))), max(1, int((K - 3.64 - 3 - 4 * b - 1.5) // 4))}):
        word = f"P{a}UL{b}"
        done = False
        for T in (3, 5, 7):
            r = mixdrop.build(word, K, '11c-5E', None, Rend=T)
            print(K, word, f"Rend={T}", r, flush=True)
            if 'halt' in r: done = True; break
        if done: break
