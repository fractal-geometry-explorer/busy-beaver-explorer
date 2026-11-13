"""Checks the binary-counter increment rule on the left records printed by c/rec18.c (EVERY = 1).

usage: ./rec18 200000 3e7 1 > r30.txt && python3 check_counter.py r30.txt

A record `n0 a 0 a d0 s1 d1 s2 ...` (head separator 1^2 0 1^2 0; s = a for 1^2 0, a digit 1, s = b for 1 0^2, a
digit 0) is followed, after the long sweep, by `n0-2 [1000] ...` with: the trailing a's of s1 s2 ... turned to b, the
first b turned to a, d0 + 2, and 2 more for the block just left of the flipped b (d0 + 4 if it is s1)."""
import sys
L = [l.split('|') for l in open(sys.argv[1]) if '|' in l]
recs = [(int(a.split()[0]), b.split()) for a, b in L]
ok = bad = other = badsmall = 0
for (s1, t1), (s2, t2) in zip(recs, recs[1:]):
    if len(t1) > 4 and t1[1] == 'a' and t1[2] == '0' and t1[3] == 'a' and t2[1] == '[1000]':
        n0 = int(t1[0]); D = int(t1[4]); s = list(t1[5:]); pred = [str(n0 - 2), '[1000]', str(D + 2)]
        i = 0; done = False
        while i < len(s):
            if s[i] == 'a':
                s[i] = 'b'; i += 2; continue
            if s[i] == 'b':
                s[i] = 'a'; done = True
                if i == 0: pred[2] = str(D + 4)
                else: s[i - 1] = str(int(s[i - 1]) + 2)
            break
        if not done:
            other += 1; continue
        blocks = [int(x) for x in ([t1[4]] + s[1:i + 2:2]) if x.isdigit()]
        pred += s; n = min(len(pred), len(t2), 40)
        if pred[:n] == t2[:n]: ok += 1
        else:
            bad += 1; badsmall += min(blocks + [99]) <= 2
print('increments following the rule', ok, 'not', bad, '(of which with a block <= 2:', badsmall, ')',
      'carry into a non-a/b token', other)
