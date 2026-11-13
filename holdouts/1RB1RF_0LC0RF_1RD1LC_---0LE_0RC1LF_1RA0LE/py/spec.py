"""The frames of the frame map (templates: blank outside, `X` the head in state X on the next cell, `u^v` v copies
of u; with TURNS a frame counts only where the head turns round)."""
M = '1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE'
FR = {'e': '11^L E 00 10^j 1^R', 'E': '1 11^L E 00 10^j 1^R', 'f': '11^L F 1^R', 'F': '1 11^L F 1^R', 'g': 'F 0 10^j 1^R', 'h': '11^L 0 11^M F 1^R', 'H': '11^L 0 1 11^M F 1^R', 'i': '1 11^L 0 11^M F 1^R', 'I': '1 11^L 0 1 11^M F 1^R', 'k': '11^L 0 1^M B', 'K': '1 11^L 0 1^M B'}
TURNS = True
MOD = 1
T, W = 4, 5
NS = 'H151878'
K = 100000000
