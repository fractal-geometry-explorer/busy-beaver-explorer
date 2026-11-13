"""The phase map of 1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD--- (proved in ../lean/Macro.lean for m = 0, 1 mod 3):
S(3j) -> S(10j+12), S(3j+1) -> S(10j+14), with the exact step counts of the proved rules
(rounds: j(6x+51) + 15j(j-1) from x = 1; zero: 4y+37, one: 4y+41 with y = 1+5j; restart: 16).
Prints the orbit from S(12) (reached at step 75) until the first m = 2 mod 3."""
t, m = 75, 12
print(m, t)
while m % 3 != 2:
    j, r = divmod(m, 3)
    y = 1 + 5 * j
    t += j * 57 + 15 * j * (j - 1) + (4 * y + 37 if r == 0 else 4 * y + 41) + 16
    m = 10 * j + 12 if r == 0 else 10 * j + 14
    print(m, t)
