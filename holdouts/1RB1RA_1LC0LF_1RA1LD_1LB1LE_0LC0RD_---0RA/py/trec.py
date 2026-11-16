"""1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA: the clean recursion as one map T, and its closed form on a run of b.

As long as no call reaches the right end of the word, the stack model (model.py) is the recursion
    F(c^a b X) = b^(a+1) T(X),      T(c^j b Y) = c F^j(c Y)   (j >= 1),      T(b Y) = c c Y.
Unfolding F once gives a recursion for T alone:

    T(b Y)             = c c Y
    T(c^j b c^i b Z)   = c b T^(j-1)( b^(i+1) T(Z) )            (j >= 1, i >= 0)

and F(b W) = b T(W): while the word starts with b, a visit is one application of T to the rest of the word.
With a = c b b:  T(a Z) = a T(Z)  (the periodic block hands every visit on).

On a run of b the map T^3 is a binary counter.  Write D(k) for the binary digits of k, lowest first, each digit
doubled, 0 as "bb" and 1 as "cc" (D(0) is empty, D(6) = bb cc cc).  Then for every k >= 0 and every word W

    T^3( b^4 D(k) b^r W ) = a  b^4 D(k+1) b^r' W ,   r' = r - 2 (number of digits of k+1 minus number of digits of k),

as long as r' >= 0.  (Behind b^4 three applications of T hand exactly one on:  T^3(b^4 c^m b Y) = a b^(4+m) T(Y).)  So T^(3k)(b^n W) = a^k b^4 D(k) b^(n - 4 - 2 len(k)) W: a run of n b's is used up only after
about 2^((n-4)/2) applications of T^3, and the visits cost O(1) transitions of the model on average.

usage: python3 trec.py rec N      T and F against model.visit on N random words (the visits that stay inside the word)
       python3 trec.py counter K  the counter rule for all k < K, with r = 6 and three words W
"""
import sys, random
sys.setrecursionlimit(1000000)


class End(Exception):
    """the recursion would read past the right end of the word"""


def T(W):
    n = len(W)
    j = 0
    while j < n and W[j] == 'c':
        j += 1
    if j >= n:
        raise End
    if j == 0:
        return 'cc' + W[1:]
    e = j + 1
    while e < n and W[e] == 'c':
        e += 1
    if e >= n:
        raise End
    U = 'b' * (e - j) + T(W[e + 1:])
    for _ in range(j - 1):
        U = T(U)
    return 'cb' + U


def F(w):
    a = len(w) - len(w.lstrip('c'))
    if a >= len(w):
        raise End
    return 'b' * (a + 1) + T(w[a + 1:])


def D(k):
    return ''.join('cc' if (k >> i) & 1 else 'bb' for i in range(k.bit_length()))


def main():
    cmd, N = sys.argv[1], int(sys.argv[2])
    if cmd == 'rec':
        import model
        random.seed(1)
        done = skipped = 0
        while done < N:
            w = ''.join(random.choice('bc') for _ in range(random.randint(1, 60)))
            try:
                v = F(w)
            except End:
                skipped += 1
                continue
            got = model.visit(w)[0]
            assert got == v, (w, got, v)
            if w[0] == 'b':
                assert v == 'b' + T(w[1:])
            done += 1
        print(f"{done} random words: F (through the one recursion for T) gives the word of the next visit of the model; "
              f"{skipped} other words reach the right end")
    elif cmd == 'counter':
        for W in ('', 'cbcccbbcb', 'ccc'):
            for k in range(N):
                r = 6
                x = 'bbbb' + D(k) + 'b' * r + W
                for _ in range(3):
                    x = T(x)
                r2 = r - 2 * ((k + 1).bit_length() - k.bit_length())
                assert x == 'cbb' + 'bbbb' + D(k + 1) + 'b' * r2 + W, (k, W)
        print(f"T^3(b^4 D(k) b^6 W) = a b^4 D(k+1) b^r' W for all k < {N} and three words W")
        random.seed(2)
        for _ in range(min(N, 20000)):
            m = random.randint(0, 6)
            Y = ''.join(random.choice('bc') for _ in range(random.randint(1, 40)))
            x = 'bbbb' + 'c' * m + 'b' + Y
            try:
                want = 'cbb' + 'b' * (4 + m) + T(Y)
            except End:
                continue
            for _ in range(3):
                x = T(x)
            assert x == want
        print("T^3(b^4 c^m b Y) = a b^(4+m) T(Y) on random words Y")
        x = 'b' * 40
        for k in range(1, min(N, 3000)):
            for _ in range(3):
                x = T(x)
            assert x == 'cbb' * k + 'bbbb' + D(k) + 'b' * (36 - 2 * k.bit_length())
        print(f"T^(3k)(b^40) = a^k b^4 D(k) b^(36 - 2 len(k)) for all k < {min(N, 3000)}")


if __name__ == "__main__":
    main()
