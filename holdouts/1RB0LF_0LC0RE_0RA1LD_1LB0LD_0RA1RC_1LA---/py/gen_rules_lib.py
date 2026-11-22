"""Shared text helpers of gen_rules.py and gen_rules_twin.py."""
from blockmm import ST


def word(toks):
    return ' '.join(str(z) for z in toks)


def describe(key, why):
    if key[0] == 'R':
        sig, kind = key[1], key[2]
        ctx = ('left context ' + ''.join(map(str, sig[2]))) if sig[0] == 'R' else \
            ('blank tape, then ' + (''.join(map(str, sig[2])) or 'nothing'))
        res = {'R': 'it comes out on the right', 'L': 'it turns back left', 'rec': 'the next left record'}[why]
        return 'Moving right in state %s (%s), crossing the word %s: %s.' % (ST[sig[1]], ctx, word(kind), res)
    lam, kind, off = key[1], key[2], key[3]
    res = {'L': 'it comes out on the left', 'R': 'it turns back right', 'rec': 'the next left record'}[why]
    return 'Moving left in state %s (right context %s), crossing the word %s%s: %s.' % (
        ST[lam[1]], ''.join(map(str, lam[2])), word(kind), ' on blank tape' if off is not None else '', res)
