"""The word rules of 1RB0RB_1LC1RA_1LF0LD_0LE1LD_1RA1LC_---1LA (and of its sibling ..._1RA1LC_---1LA, which has the
same sweeps and other resets), at three levels:

* bits: the tape at a turn is a word W over pairs, 1 = `11`, 0 = `01`, read left to right, the head (C) on the last
  pair, which is always 1.  `sweep_bits(W)`: find the rightmost `00` in W, at positions (i, i+1); flip W[i-1];
  replace W[i+1..] by its differences W[k] ^ W[k+1] (rule 102); append `11`.  No `00` at all: a reset
  (`reset_bits`).  The `00` at the very start (i = 0): the machine halts.  A sweep costs 4 (n - i + 1) steps.
* digits: W = 1^w then, for each digit k, `0 1^k` (on the tape: the wall 1^(2w), then blocks 1^(2k+1) separated by
  single 0s).  `sweep_digits`: the rightmost zero digit j; case A (left neighbour >= 1): it loses 1 and a new zero
  stands after it; case B (left neighbour 0): the two zeros go and the digit before gains 1; the digits after j
  become T(D).
* runs: the digits run-length coded, for long runs (`Runs`).

Everything here is checked against the machine by check.py."""

VARIANT = "35"


def nand_seq(W):
    n = len(W)
    return [None] + [1 - (W[k] & W[k + 1]) for k in range(n - 1)] + [1]   # N[1..n], 1-based


def reset_bits(W, variant=None):
    """The word after a reset (no 00 in W), as the first turn at the right end afterwards."""
    v = variant or VARIANT
    n = len(W)
    N = nand_seq(W)
    a, b = W[0], W[1]
    if v == "34":
        if (a, b) == (0, 1):
            return [1, 1] + N[2:n + 1] + [1]
        if (a, b) == (1, 1):
            return [1, 1 - N[2]] + N[3:n + 1] + [1, 0, 1]
        if (a, b) == (1, 0):
            return [1, 0, 0, 0] + N[2:n + 1] + [1]
    if v == "35":
        if (a, b) == (0, 1):
            return [0, 1] + N[2:n + 1] + [1]
        if (a, b) == (1, 1):
            if n == 2:
                return [0, 0, 1, 0, 1]
            return [0, 1 - N[2]] + N[3:n] + [1, 1, 0, 1]
        if (a, b) == (1, 0):
            return [0, 1, 0] + N[3:n] + [1, 1, 0, 1]
    raise ValueError("no reset rule")


def sweep_bits(W):
    """('ok', W', cost) | ('reset', None, None) | ('halt', None, cost)"""
    n = len(W)
    i = None
    for k in range(n - 2, -1, -1):
        if W[k] == 0 and W[k + 1] == 0:
            i = k
            break
    if i is None:
        return 'reset', None, None
    if i == 0:
        return 'halt', None, None
    out = W[:i - 1] + [1 - W[i - 1], 0] + [W[k] ^ W[k + 1] for k in range(i + 1, n - 1)] + [1, 1]
    return 'ok', out, 4 * (n - i + 1)


def to_digits(W):
    p = 0
    while p < len(W) and W[p] == 1:
        p += 1
    w, K = p, []
    while p < len(W):
        p += 1
        k = 0
        while p < len(W) and W[p] == 1:
            k += 1
            p += 1
        K.append(k)
    return w, K


def to_bits(w, K):
    b = [1] * w
    for k in K:
        b += [0] + [1] * k
    return b


def T(D):
    """The digits after a sweep's zero, from the zero-free digits D after it."""
    out, i, m = [], 0, 0
    while i < len(D) and D[i] == 1:
        m += 1
        i += 1
    out.append(1 + 2 * m)
    while i < len(D):
        d = D[i]
        i += 1
        m = 0
        while i < len(D) and D[i] == 1:
            m += 1
            i += 1
        out += [0] * (d - 2) + [2 + 2 * m]
    return out


def sweep_digits(w, K):
    j = None
    for t in range(len(K) - 1, -1, -1):
        if K[t] == 0:
            j = t
            break
    if j is None:
        return 'reset', None
    D = K[j + 1:]
    left = w if j == 0 else K[j - 1]
    if j == 0 and w == 0:
        return 'halt', None
    if left >= 1:
        if j == 0:
            return 'ok', (w - 1, [0] + T(D))
        return 'ok', (w, K[:j - 1] + [K[j - 1] - 1, 0] + T(D))
    if j == 1:
        return 'ok', (w + 1, T(D))
    return 'ok', (w, K[:j - 2] + [K[j - 2] + 1] + T(D))


# ---- run-length coded digits, with exact step counts ----

def _push(out, v, c):
    if c <= 0:
        return
    if out and out[-1][0] == v:
        out[-1][1] += c
    else:
        out.append([v, c])


def T_runs(D):
    out = []
    idx = 0
    m = 0
    if idx < len(D) and D[idx][0] == 1:
        m = D[idx][1]
        idx += 1
    _push(out, 1 + 2 * m, 1)
    while idx < len(D):
        d, c = D[idx]
        idx += 1
        m = 0
        if idx < len(D) and D[idx][0] == 1:
            m = D[idx][1]
            idx += 1
        if d == 2:
            _push(out, 2, c - 1)
        else:
            for _ in range(c - 1):
                _push(out, 0, d - 2)
                _push(out, 2, 1)
        _push(out, 0, d - 2)
        _push(out, 2 + 2 * m, 1)
    return out


class Runs:
    """wall w and runs [[digit, count], ...]; sweep() returns 'ok' (and adds the step count to self.t), 'reset' or
    'halt'.  self.n is the word length (bits)."""

    def __init__(self, w, K, t=0):
        self.w = w
        self.R = []
        for k in K:
            _push(self.R, k, 1)
        self.t = t
        self.n = w + sum(1 + k for k in K)

    def digits(self):
        K = []
        for v, c in self.R:
            K += [v] * c
        return self.w, K

    def bits(self):
        return to_bits(*self.digits())

    def sweep(self):
        R = self.R
        t = len(R) - 1
        tail_bits = 0
        while t >= 0 and R[t][0] != 0:
            tail_bits += R[t][1] * (1 + R[t][0])
            t -= 1
        if t < 0:
            return 'reset'
        # n - i: bits from the rightmost zero digit (one bit) to the end
        cost = 4 * (1 + tail_bits + 1)
        D = R[t + 1:]
        del R[t + 1:]
        c = R[t][1]
        if c >= 2:
            R[t][1] -= 2
            if R[t][1] == 0:
                R.pop()
            if R:
                v = R[-1][0]
                R[-1][1] -= 1
                if R[-1][1] == 0:
                    R.pop()
                _push(R, v + 1, 1)
            else:
                self.w += 1
        else:
            R.pop()
            if R:
                v = R[-1][0]
                if v == 0:
                    R[-1][1] -= 1
                    if R[-1][1] == 0:
                        R.pop()
                    if R:
                        v2 = R[-1][0]
                        R[-1][1] -= 1
                        if R[-1][1] == 0:
                            R.pop()
                        _push(R, v2 + 1, 1)
                    else:
                        self.w += 1
                else:
                    R[-1][1] -= 1
                    if R[-1][1] == 0:
                        R.pop()
                    _push(R, v - 1, 1)
                    _push(R, 0, 1)
            else:
                if self.w == 0:
                    return 'halt'
                self.w -= 1
                _push(R, 0, 1)
        for v, cc in T_runs(D):
            _push(R, v, cc)
        self.t += cost
        self.n += 1
        return 'ok'
