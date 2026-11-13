"""The frames of the frame map (templates: blank outside, `X` the head in state X on the next cell, `u^v` v copies
of u; with TURNS a frame counts only where the head turns round)."""
M = '1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC'
FR = {'b': '1^L B 10 10^j 1^R', 'a': '1^L 10^j 110 A 1^R', 'c': '1^L 0 C 0 10^j 1^R', 'd': '1^L A 01 10^j 1^R', 'e': '1^L 10^j B', 'f': '1^L 10^j 1101 B'}
TURNS = True
MOD = 1
T, W = 4, 5
NS = 'H8084'
K = 100000000
