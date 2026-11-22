"""The layers of the digit-only end Z of the tape (dumps written by c/toksim.cpp).

usage: python3 py/layers.py DUMP_K DUMP_K2     (two dumps of rounds k < k2 with k2 - k a multiple of 56)

Z is read lowest digit first. From its top down: a stretch of period 4 (the expansion of 1/15), then one of
period 28 (1/15 minus a multiple of 1/127, see py/vasym.py), then a stretch that is the same in round k and in
round k2 (aligned at the bottom of the period-28 stretch: frozen digits), and below it the irregular digits,
the only ones the round's defect ever eats.
"""
import sys


def zpart(path):
    s = open(path).read().strip()
    j = len(s)
    while j > 0 and s[j - 1] in 'OI': j -= 1
    return s[j:]


def pstart(z, end, p):
    i = end - 1
    while i - p >= 0 and z[i] == z[i - p]: i -= 1
    return i - p + 1


a, b = zpart(sys.argv[1]), zpart(sys.argv[2])
sa = pstart(a, pstart(a, len(a), 4), 28); sb = pstart(b, pstart(b, len(b), 4), 28)
m = 0
while sa - m - 1 >= 0 and a[sa - m - 1] == b[sb - m - 1]: m += 1
s4 = pstart(a, len(a), 4)
print('|Z| = %d: period 4: %d, period 28: %d, frozen: %d, irregular: %d' % (len(a), len(a) - s4, s4 - sa, m, sa - m))
