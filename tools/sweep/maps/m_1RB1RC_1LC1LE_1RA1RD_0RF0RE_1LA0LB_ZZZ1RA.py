"""1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA: lean/Macro.lean `S2`, `next`; lean/Reduction.lean `orbit`,
`halts_iff`, `halts_iff'`.

R n m = A> 0 11 (01)^n 0 11 (01)^m (state ("r", n, m)), Z k = A> 0 11 (01)^k (state ("z", k)).
next r(n, m) = r(3(n div 2)+2, m+2) for n even; z(3(n div 2)+6) for n odd, m = 0; r(3(n div 2)+5, m-1) for n odd,
m >= 1.  next z(k) = none (halt) for k even, r(3(k div 2)+2, 1) for k odd.  Halts from blank iff the orbit of z(1)
reaches none, i.e. some z(k) with k even (halts_iff').
"""

MACHINE = "1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA"
LEAN = ("holdouts/1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA/lean/Macro.lean: S2, next; "
        "lean/Reduction.lean: orbit, halts_iff, halts_iff'")
VARS = ("tag", "n (k for z)", "m (absent for z)")
START = ("z", 1)
HALT = "z(k) with k even (reached from r(n, 0) with n odd)"
KIND = "parity-3/2"
BOUND = "1e5 rounds (status.json, Python py/orbit.py; counter m = 50,008 at the end); 10,000 rounds Lean kernel (first_rounds)"


def step(s):
    if s[0] == "z":
        k = s[1]
        if k % 2 == 0:
            return None, "zH"
        return ("r", 3 * (k // 2) + 2, 1), "z"
    _, n, m = s
    if n % 2 == 0:
        return ("r", 3 * (n // 2) + 2, m + 2), "e"
    if m == 0:
        return ("z", 3 * (n // 2) + 6), "o0"
    return ("r", 3 * (n // 2) + 5, m - 1), "o"


# no margin: the halting test is a small counter m reaching 0 then a parity coin (m drifts up by 1/2 per round)
