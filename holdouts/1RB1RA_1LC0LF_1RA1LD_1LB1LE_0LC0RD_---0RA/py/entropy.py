"""1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA: how compressible are the words of the run from blank tape?

An accelerator that skips whole cascades needs a short description of the word (runs with large exponents, repeated
units, a ladder of levels).  This script measures what there is to describe: the word of visit V is  b a^k R
(a = c b b), and for R it prints the number of tokens, the number of runs of equal letters, the tokens left over when
every repetition u^n (|u| <= 40, n >= 4) is taken out, and the size of R under LZMA in bits.  With `rewrite` it
compares the words before and after a visit that reaches the right end: the common suffix (what the visit left alone).

usage: python3 entropy.py WRUN [V ...]            (WRUN: the compiled c/wrun.c; default V: 2^10 .. 2^18)
       python3 entropy.py WRUN rewrite [V ...]    (default V: 32497 50841 113145 118809 231897)
       python3 entropy.py WRUN prefix V1 V2       (the common prefix of the words of two visits)
"""
import sys, subprocess, lzma

EXP = {'a': 'cbb', 'b': 'b', 'c': 'c'}


def word(wrun, v):
    out = subprocess.run([wrun, 'wordat', str(v)], capture_output=True, text=True, check=True).stdout.split()
    return ''.join(EXP[x[0]] * int(x[1:]) for x in out)


def literal(s, maxp=40, minrep=4):
    """tokens of s outside every repetition u^n with |u| <= maxp, n >= minrep (greedy, left to right)"""
    i, n, lit = 0, len(s), 0
    while i < n:
        best = 0
        for p in range(1, maxp + 1):
            if i + minrep * p > n:
                break
            j = i + p
            while s.startswith(s[i:i + p], j):
                j += p
            if j - i >= minrep * p and j - i > best:
                best = j - i
        if best:
            i += best
        else:
            lit += 1
            i += 1
    return lit


def runs(s):
    return sum(1 for i in range(len(s)) if i == 0 or s[i] != s[i - 1])


def main():
    wrun = sys.argv[1]
    args = sys.argv[2:]
    if args and args[0] == 'rewrite':
        vs = [int(x) for x in args[1:]] or [32497, 50841, 113145, 118809, 231897]
        for v in vs:
            x, y = word(wrun, v), word(wrun, v + 1)
            k = 0
            while k < min(len(x), len(y)) and x[-1 - k] == y[-1 - k]:
                k += 1
            print(f"visit {v} (reaches the right end): {len(x)} tokens before, {len(y)} after, common suffix {k} tokens")
        return
    if args and args[0] == 'prefix':
        x, y = word(wrun, int(args[1])), word(wrun, int(args[2]))
        k = 0
        while k < min(len(x), len(y)) and x[k] == y[k]:
            k += 1
        print(f"visits {args[1]} and {args[2]}: {len(x)} and {len(y)} tokens, common prefix {k} tokens")
        return
    vs = [int(x) for x in args] or [2 ** e for e in range(10, 19)]
    print("visit    tokens  a-block  rest R  runs in R  outside repetitions  LZMA bits  bits per token of R")
    empty = 8 * len(lzma.compress(b''))
    for v in vs:
        w = word(wrun, v)
        s = w[1:] if w[0] == 'b' else w
        k = 0
        while s.startswith('cbb', 3 * k):
            k += 1
        r = s[3 * k:]
        bits = 8 * len(lzma.compress(r.encode(), preset=9)) - empty
        print(f"{v:<8d} {len(w):<7d} {k:<8d} {len(r):<7d} {runs(r):<10d} {literal(r):<20d} {bits:<10d} {bits / max(1, len(r)):.2f}")


if __name__ == "__main__":
    main()
