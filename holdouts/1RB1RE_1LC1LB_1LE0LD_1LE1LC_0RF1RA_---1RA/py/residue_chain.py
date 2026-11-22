"""usage: python3 residue_chain.py MOD MAXLEN SAMPLES SEED   (the chains in lean/NoParityInvariant.lean: 2 12 300 1, 4 12 300 1, 8 12 300 1, 16 18 400 1)

Search for a chain of lists of D refuting every residue-word invariant mod MOD.
Residue word of l: [r % MOD for r in l].  A set S of residue words closed under the visit map (for every l in D with
word in S, the word of visit(l) is in S) and containing the word of l0 contains the word of a list that halts.
Output: JSON chain [l_1..l_n], word(l_1)=word(l0), word(visit l_i)=word(l_{i+1}), visit(l_n)=None."""
import sys, os, random, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from visit import visit, inD
MOD, MAXLEN, SAMP, SEED = map(int, sys.argv[1:5])
random.seed(SEED)
w = lambda l: tuple(r % MOD for r in l)
L0 = [12] + [1] * 9
def realize(word):
    for _ in range(SAMP):
        l = [random.choice([v for v in range(c or MOD, 6 * MOD + 8, MOD) if v != 2]) for c in word]
        l[0] = random.choice([v for v in range(12, 12 + 4 * MOD) if v % MOD == word[0]])
        if random.random() < 0.2 and word[:4] == w([6, 4, 1, 1]): l[:4] = [6, 4, 1, 1]
        if inD(l): yield l
start = w(L0); par = {start: None}; fr = [start]; d = 0
while fr:
    d += 1; nf = []
    for word in fr:
        for l in realize(word):
            r = visit(l)
            if r is None:
                ch = [l]; x = word
                while par[x]: ch.append(par[x][1]); x = par[x][0]
                ch.reverse()
                assert w(ch[0]) == start and visit(ch[-1]) is None and all(inD(a) for a in ch)
                assert all(w(visit(a)) == w(b) for a, b in zip(ch, ch[1:]))
                json.dump(ch, open("chain%d.json" % MOD, "w")); print("MOD", MOD, "chain of", len(ch)); sys.exit()
            s = w(r)
            if len(s) <= MAXLEN and s not in par: par[s] = (word, l); nf.append(s)
    fr = nf
print("MOD", MOD, "no chain within bounds; words", len(par))
