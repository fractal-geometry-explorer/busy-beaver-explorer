"""The frames of the frame map (templates: blank outside, `X` the head in state X on the next cell, `u^v` v copies
of u; with TURNS a frame counts only where the head turns round)."""
M = '1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD'
FR = {'z': '1^L 10^j C 1^R', 'y': '1^L A 10 10^j 1^R', 'w': '1^L C 00 10^j 1^R', 'u': '1^L 10^j 1 A 00 1^R', 'Z': '1110 1^L 10^j C 1^R', 'Y': '1110 1^L A 10 10^j 1^R', 'W': '1110 1^L C 00 10^j 1^R', 'U': '1110 1^L 10^j 1 A 00 1^R'}
TURNS = True
MOD = 1
T, W = 4, 5
NS = 'H97525'
K = 100000000
