"""1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE: lean/Orbit.lean `phase`, `next`, `orbit`, `halts_iff`."""
from maps._common import Stuck, bl

MACHINE = "1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE"
LEAN = "holdouts/1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE/lean/Orbit.lean: phase, next, orbit, halts_iff"
VARS = ("N",)
START = (22,)
HALT = "the doublings (K,m) -> (2K+4, m-2K-6) from (1,N) leave m = 0"
KIND = "power-of-2"
BOUND = "1e6 rounds, N then 666,845 bits (status.json, py/orbit.py)"


def phase(K, m):
    """Lean `phase`, its tail recursion unrolled.  Returns (N' or None, number of doublings)."""
    j = 0
    while True:
        if m == 0:
            return None, j
        if 2 * K + 6 <= m:
            K, m = 2 * K + 4, m - (2 * K + 6)
            j += 1
            continue
        return 2 * K + 3 * m + 2, j


def step(s):
    (N,) = s
    if N % 2:
        raise Stuck("N odd is outside phase_spec (orbit values are even)")
    N2, j = phase(1, N)
    if N2 is None:
        return None, "H"
    return (N2,), "r"


def remainder(N):
    """The m left after the doublings from (1, N), by the plain loop (slow for big N; used for validation)."""
    K, m = 1, N
    while 2 * K + 6 <= m:
        K, m = 2 * K + 4, m - (2 * K + 6)
    return m


def doublings(N):
    """(j, m): the number of doublings from (1, N) and the remainder, in closed form (K_j = 5*2^j - 4,
    m_j = N + 10 - 10*2^j + 2j; the loop runs while N + 12 + 2j >= 20*2^j)."""
    j = max(0, (N + 12).bit_length() - 6)
    while j > 0 and N + 12 + 2 * (j - 1) < 20 * (1 << (j - 1)):
        j -= 1
    while N + 12 + 2 * j >= 20 * (1 << j):
        j += 1
    return j, N + 10 - 10 * (1 << j) + 2 * j


def margin(s):
    return bl(doublings(s[0])[1])


def accel(s):
    """One `step` with the doubling loop in closed form: after j doublings from (1, N), K = 5*2^j - 4 and
    m = N + 10 - 10*2^j + 2j; the loop stops at the least j with m < 2K + 6 = 10*2^j - 2 (or m = 0 first)."""
    (N,) = s
    if N % 2:
        raise Stuck("N odd is outside phase_spec (orbit values are even)")
    # Lean checks m = 0 before each doubling; m_i >= 10*2^i - 2 > 0 while the loop runs, so only the last can be 0
    j, m = doublings(N)
    if m == 0:
        return None, 1, "H"
    K = 5 * (1 << j) - 4
    return (2 * K + 3 * m + 2,), 1, "r"
