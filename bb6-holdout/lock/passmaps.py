"""The pass maps of the one-extra-wall loop, on (w1, w2, w3, w4, E) at a pass start G 1, W w1 … W w4, width E.
Rows: new position = sum(coef * old) + const.  Read off the forced runs (`../conc/ewmap.py`) and checked on the proved
model by `verify_maps.py`."""
from fractions import Fraction as F
def _m(rows): return [[F(x) for x in r] for r in rows]
#                 w1  w2       w3      w4      E        const
P = _m([[0, '1/64', '1/64', 0, 0, '271/64'],
        [0, '1/64', '5/64', '3/16', '1/4', '899/64'],
        [0, 0, '1/16', '1/4', '11/16', '179/8'],
        [0, 0, 0, '1/16', '15/16', '369/16'],
        [0, 0, 0, 0, 1, 24]])
Q = _m([[0, '1/128', 0, 0, 0, '257/64'],
        [0, '9/128', '1/32', '1/8', '1/4', '855/64'],
        [0, '1/16', '1/32', '3/16', '11/16', '701/32'],
        [0, 0, 0, '1/16', '15/16', '369/16'],
        [0, 0, 0, 0, 1, 24]])
MAPS = {'P': P, 'Q': Q}
def apply(M, x):
    return [sum(r[j] * x[j] for j in range(5)) + r[5] for r in M]
