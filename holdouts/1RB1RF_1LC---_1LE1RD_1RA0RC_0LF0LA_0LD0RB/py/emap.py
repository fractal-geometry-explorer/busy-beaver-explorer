"""The exact left-end map of 1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB.

A state (s, n, k): the head in state s = 'A' two cells (s = 'D': three cells) left of the tape
1^n (01)^k 111  (k >= 1)  or  1^n  (k = 0), everything else blank.  `step` is the next such state, or 'HALT'.
`jump` does a whole run of drain steps at once."""


def step(s, n, k):
    o = 'D' if s == 'A' else 'A'
    if k == 0:
        if n % 2 == 0:
            return (o, n + 3, 0)
        return ('D', 1 if s == 'A' else 3, (n + 1) // 2)
    if n % 2 == 0:
        return (o, n + 4, k - 1) if k >= 2 else (o, n + 7, 0)
    if k == 1:
        return 'HALT'
    c = 7 if s == 'D' else 6
    if 2 * k > n + 5:
        return (s, 2 * n + c, k - (n + 5) // 2)
    if 2 * k == n + 5:
        return (s, 2 * n + c + 3, 0)
    return (o, n - 2 * k + 6, 2 * k)


def jump(s, n, k):
    """step, but a run of drain steps (n even, k >= 2) in one go."""
    if k >= 2 and n % 2 == 0:
        j = k - 1
        return (s if j % 2 == 0 else ('D' if s == 'A' else 'A'), n + 4 * j, 1)
    return step(s, n, k)
